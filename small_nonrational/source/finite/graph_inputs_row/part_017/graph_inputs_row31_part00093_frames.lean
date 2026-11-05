module
prelude
public import GraphInputsRow31Part00093Data
public import RawFrameSupport
public import SharedFrameGroups034Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xdb5601a8e5450a0f4e1a6d133e98d4af253d27492847da3d51a48bb451222d07882e3fe1fb8fb87a23c69d58e827163721b44cdc60d2f21750b1a5802b99590a7052b28f143c9d04ca25b929892844e20f90387ec3af1cf8e346fa34f19f8cb463a2f51678ae854428c12508403da1d70e206d43441830bb85a42be1520a304e025c11b08503d81d00b0057827012408e04601e00dc06a03481680aa054020810006e03601980c806202f01700a004802200f807403801800b804801c00d004802000e0060028008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe2163baa85520a7650fa81d3d89d74ce26292ee96548b241d1d28d746222c90c685441da0d50487f03ee9eb8f3e7313821bd4d0e6593191888ba25c22d91678ad655e2a915109f24de268931496e46c22a911485a3d61e08ea07283601a80cf865e2eb15f8abc53a28e125088840c1ee0ee072836a18e0be059c2ac14809e04b824810b07f83c41ce0b0057827012408e04601e00dc06a03481680aa054020810006e03601980c806202f01700a004802200f807403801800b804801c00d004802000e0060028008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x3e1730d019fb3e672ccd9632362ec45853015daba171add5acb355cab454ea8950a97524a1d4126b4c096d2222d4568a91222043684d02a013f87d0ef9d93aa740e41b334c694d199b32862cc19702d2580ac13f2684b49211c2063c8758e81c637c6b0cd18e3045d8b61602a85209c12c2404507a0f21c03586a0d21782c0570ac130238460720e01883005e0b81682c0560981102003a06c0d01802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0x3cae0729ca327c871bc530ec0afcbd6efb72d7b46cbb12beaaea6a6694a4e89a12799d25d94a4d8da1f8761c8561082e047ddf27b5e674dcc71dc26eda866d9a6618f621815e56758159545394b92748118400ef3a0e5380db350cd31cc12ecb62c0aa2909c258902287a1e46e1a0671985b1545414c4a114440dc360bc2e0b42c0ac2a0a426088200741b0681805c120380d0240801c060140200400 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1060.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1060.count (({ width := 10, code := 0x246861e478de277ddd765d5741ce729c66e9b66cdb16b5a96759963d8b629846097c5e96a5916254942505404f13a4e1354b52b4a52645d134450f430fd3c8f13bceb3a0e437cd7350d032cbe2dcb42c0ab278922348c2288720c811f4781dc751c46c1ac681905f1785a1645815c561544e128491203f0e8390c8310b42c0ac2a0a42809c240801e06c1906017058120380d0240801c060140200400 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1060
    Papers.RationalityTen.SharedFrameCatalogue.group1060_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb18a068d08b98b188a87f86d85e83b82e81d80a7b97a579478477076170d6fd6c26b269868a68467466d63a62761f5e259d5565535335295205134ee4e34db4cd47d46c45f4534453f23b539d39536e3613513443213143042f42bb2972872742662251e61c21b71ab19e18f17316515314513712b11910a0f30e80d80cd0a009f09608c08808607606c06806705805305204104003703603303203102f02e02802402201f01d01c01801701200e00d009008007006005002001000 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x6a7c6765ac6d87ae35a2add4fa794c693d1b9d3372694cb9792d23ec708bd1622643e8770c61640a7f8fdde93b673ee71bfb776e0d91a634367ecd57f2f25d6b8d6e2a251ea1940a654b493921229442869089e93a6730e11bb3225d4b195929e5149d1252344247e0f41d43846c8c61842d45688c1162083e07a0f01a4310600be1402584a07a0f01a8340660c81882f05c0a01202203e0740e01802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0618.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0618.count (({ width := 9, code := 0x1389a47a3b1c8dc6a33188b456291387432170a84c2207017ebedf4f97c3ddecee76bb1c8dc6db69b2d86bb59a8d36934596ca64b218ec15e2ed74b659abd58a651a7d389346a290c833d1c4dc6d361acd46631984be5c2c95caa502692c924321104803f1f0ec72381b8c85e2e158a85027130944823110843e1d0e06832170b0481c0d048200e06028080200 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame008_links_0000 record000_frame008_links_0064)
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0618
    Papers.RationalityTen.SharedFrameCatalogue.group0618_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x72964e58257256c55a55354e54753853152b5245074fe4f44ed4e74e04c44bc4a649e49549048a47d47845644b44640e3dc3a239e37d37336a36334a3423393303012f02e82e32db2a727b26825e24023923022620c2031fb1f31cc1b31ab1a419c17114612912111a11410d1040fd0f60f00eb0e50de0d70cb0c50bf0ba09a09908e08608208007406c06806705805305204104003703603303203102f02e02802402201f01d01c01801701200e00d009008007006005002001000 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame009_links_0000 record000_frame009_links_0064)
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x3fd74ad49a534465eca59131f624c3d853045dcba5712dd5aeb495e2b654aa854d296526a4146a7c4e89c5322564828f115a2844a8850a20f41a81cf61e03b675ce89b4340658c817d2ee5c4b61632be56cac14326c4c09412321e3d8748e31ba35c688c71802f05b8b21562905189a12a2404587e0fa1d43886e0d81902f85c0b61382484807a0f01b8360660c81882f05c0a01202203e0740e01802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame010_links_0000 record000_frame010_links_0064)
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
def record000_frame011_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x53394706607c0b7f8fe1f93ee7baf55e7bcc762ea5d039d72ce39b8b6b6b6d55a7b4a68ecf99c31c628c39792cf56cad150299520a2d3ca754e09b1262404748d1172053da790f11ce392700dc9a433c658c816f2b8560a994f268478881082063f07b8ed1d23886e0d71a4338648be1722c8588941262184087d0f81b8348660ca1582885007e0f81a8340620c01782d05809c1182103c0700d81802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record000) (record000.maps 11)
      (record000.inverseMaps 11) record000_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame011_links_0000 record000_frame011_links_0064)
theorem record000_frame011_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 11 :=
  of_group record000 11 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record000_frame011_indices record000_frame011_graph record000_frame011_links
def record000_frame012_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0969.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0969.count (({ width := 9, code := 0xf374b7dbcdd6e36db2d86b355a6d26733196ca6431d86c15f2f176ba5bad966ad562a5469d4e26d34984b251269147a35108742a0d027c3b9d8ea74391c4de6d359a8d0633097cbc5c2b948a04f269309449241188a4421904803e1e8ec74371b0cc6230178b054291409446220e87032180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record000_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0969.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record000) (record000.maps 12)
      (record000.inverseMaps 12) record000_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame012_links_0000 record000_frame012_links_0064)
theorem record000_frame012_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 12 :=
  of_group record000 12 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0969
    Papers.RationalityTen.SharedFrameCatalogue.group0969_facts record000_frame012_indices record000_frame012_graph record000_frame012_links
def record000_frame013_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0972.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0972.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0972.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0972.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0972.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0972.localPairCheck (smallEmbedding record000) (record000.maps 13)
      (record000.inverseMaps 13) record000_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame013_links_0000 record000_frame013_links_0064)
theorem record000_frame013_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 13 :=
  of_group record000 13 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0972
    Papers.RationalityTen.SharedFrameCatalogue.group0972_facts record000_frame013_indices record000_frame013_graph record000_frame013_links
def record000_frame014_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0966.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0966.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0966.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0966.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0966.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0966.localPairCheck (smallEmbedding record000) (record000.maps 14)
      (record000.inverseMaps 14) record000_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame014_links_0000 record000_frame014_links_0064)
theorem record000_frame014_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 14 :=
  of_group record000 14 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0966
    Papers.RationalityTen.SharedFrameCatalogue.group0966_facts record000_frame014_indices record000_frame014_graph record000_frame014_links
def record000_frame015_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x39968cbed79af25d6ba1722e15b0b51682cd574ad1572a7544a7942a7f4da99d3125d4b694d28a4046e8d5112073d47a0ee9d83aa740e31bf3786dcce198326640c516f2ba560aa94a28c5049f13425e4a09290e20a3f87b8f41c0334618c01742d8590ac1522985189f13625c4988e116218418780ee1c83686b0d21902f85c0b6138248480821001b8360660c81882f05c0a01202203e0740e01802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 15) (record000.inverseMaps 15) record000_frame015_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 15) (record000.inverseMaps 15) record000_frame015_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 15)
      (record000.inverseMaps 15) record000_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame015_links_0000 record000_frame015_links_0064)
theorem record000_frame015_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 15 :=
  of_group record000 15 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record000_frame015_indices record000_frame015_graph record000_frame015_links
def record000_frame016_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x5b3a532964cc928ef1ae3145b88f10a1cc31817011fdbf37d8f99e2bbc742e61c8b866fedddb9355690d0d8daf45b6b5d61abd572acd50a9b52ca39352604ae945242213fc7d4f79d93a071ce01b1356694d11872f65c4b396127e470869072023f07a8ed1cc3806d0d419c318610b91662b0538921222204107e0f81cc358680ce160298520821001b8360660c81882f05c0a01202203e0740e01802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record000) (record000.maps 16) (record000.inverseMaps 16) record000_frame016_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record000) (record000.maps 16) (record000.inverseMaps 16) record000_frame016_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record000) (record000.maps 16)
      (record000.inverseMaps 16) record000_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame016_links_0000 record000_frame016_links_0064)
theorem record000_frame016_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 16 :=
  of_group record000 16 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record000_frame016_indices record000_frame016_graph record000_frame016_links
def record000_frame017_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x4577cade9b9b726d6d99b135e6a2d31a4345660ca99232063ac6580afc5d8b95712d55a4b29622a3534a5539a4f4708d911a1b42c845032003fa7e4ee1d239a728e29a5322634c517b2ea5bcb39572a653ca492f24647c8d9191fa3a46f8d81a8340650c51842f85d8b91682c4560a61482784d0800fe1e0398700dc1943085e0ba1482684c0760e81983205e0b81682b0540981102003a06c0d01802e0480700d0120200380600a00800800 } : Fields).get c.val)
theorem record000_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 17) (record000.inverseMaps 17) record000_frame017_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 17) (record000.inverseMaps 17) record000_frame017_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 17)
      (record000.inverseMaps 17) record000_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame017_links_0000 record000_frame017_links_0064)
theorem record000_frame017_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 17 :=
  of_group record000 17 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record000_frame017_indices record000_frame017_graph record000_frame017_links
def record000_frame018_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0528.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0528.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605e5d5c5b5a595857565554535251504f4e4d4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a2928272625242322201f1e1d1c1b1a1918171514131211100f0e0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0528.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0528.localPairCheck (smallEmbedding record000) (record000.maps 18) (record000.inverseMaps 18) record000_frame018_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0528.localPairCheck (smallEmbedding record000) (record000.maps 18) (record000.inverseMaps 18) record000_frame018_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0528.localPairCheck (smallEmbedding record000) (record000.maps 18)
      (record000.inverseMaps 18) record000_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame018_links_0000 record000_frame018_links_0064)
theorem record000_frame018_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 18 :=
  of_group record000 18 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0528
    Papers.RationalityTen.SharedFrameCatalogue.group0528_facts record000_frame018_indices record000_frame018_graph record000_frame018_links
def record000_frame019_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0529.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0529.count (({ width := 8, code := 0xdcd2c8c7c6c5c3c1c0bfbdbbbab6b4b3b1afaeaaa8a4a2a19f9d9b9993918f89838281807e7c7b7a78767571706e6c6b67636261605e5d5c5a58575652504e4d4c48444241403f3e3d3c3b3a39383736343332312e2d2a2827262321201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0529.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0529.localPairCheck (smallEmbedding record000) (record000.maps 19) (record000.inverseMaps 19) record000_frame019_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0529.localPairCheck (smallEmbedding record000) (record000.maps 19) (record000.inverseMaps 19) record000_frame019_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0529.localPairCheck (smallEmbedding record000) (record000.maps 19)
      (record000.inverseMaps 19) record000_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame019_links_0000 record000_frame019_links_0064)
theorem record000_frame019_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 19 :=
  of_group record000 19 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0529
    Papers.RationalityTen.SharedFrameCatalogue.group0529_facts record000_frame019_indices record000_frame019_graph record000_frame019_links
def record000_frame020_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0527.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0527.count (({ width := 8, code := 0xdcd2c8c7c6c5c3c1c0bfbdbbbab6b4b3b1afaeaaa8a4a2a19f9d9b9993918f89838281807e7c7b7a78767571706e6c6b67636261605e5d5c5a58575652504e4d4c48444241403f3e3d3c3b3a39383736343332312e2d2a2827262321201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0527.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0527.localPairCheck (smallEmbedding record000) (record000.maps 20) (record000.inverseMaps 20) record000_frame020_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0527.localPairCheck (smallEmbedding record000) (record000.maps 20) (record000.inverseMaps 20) record000_frame020_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0527.localPairCheck (smallEmbedding record000) (record000.maps 20)
      (record000.inverseMaps 20) record000_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame020_links_0000 record000_frame020_links_0064)
theorem record000_frame020_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 20 :=
  of_group record000 20 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0527
    Papers.RationalityTen.SharedFrameCatalogue.group0527_facts record000_frame020_indices record000_frame020_graph record000_frame020_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (Fin.cases (record000_frame011_supported hcells) (Fin.cases (record000_frame012_supported hcells) (Fin.cases (record000_frame013_supported hcells) (Fin.cases (record000_frame014_supported hcells) (Fin.cases (record000_frame015_supported hcells) (Fin.cases (record000_frame016_supported hcells) (Fin.cases (record000_frame017_supported hcells) (Fin.cases (record000_frame018_supported hcells) (Fin.cases (record000_frame019_supported hcells) (Fin.cases (record000_frame020_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093
