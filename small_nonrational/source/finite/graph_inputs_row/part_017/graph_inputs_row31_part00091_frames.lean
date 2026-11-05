module
prelude
public import GraphInputsRow31Part00091Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups009Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091
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
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x40680b01200c007fcfedf8be77b4f5de6bc377eeedd7bac748e7dc6383700de9bbb756ccd61a7b4a688d019eb2f64cc2980ae25bab5d692cd580af1552a1528a39432814fa9cd31a5549691d1ba3645689909a0d412804f99f23c075ce51a434062cc517d2f25c0b515b2ac51ca0936250478879081c63806b8d419a31c5e8bc1642a05189a12022c3d0760e21b0338650b816c2985009c124240470740dc1903105e0a01101f03a0700c00e01a0240400700c00800800 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record005_frame001_links_0000 (interval_append _ 64 128 133 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe9b730387dc38dcd6e0b639a68d2867ab2498dec31601afdd78eb9e5c6ad856aab2557e2bad56caa154e2a414eca6b52a287d3f899c4c525dd2ca95a49624591d28d746222c914e879431a0ed06a8273f29eccf487713a31cd8e126fa3639a70d1865732118f8c7062230b9810bac5bc2b8158caa454429e145ca084e326b131496e4af24511dc8b24552168e4c67c32f17e8b7453a28e12e08f040c1ca0da863829013c092042c1fe0e705982c015009c049023811806a03481840b405502a00c8062029011007403801800b805001c00d004802000e0060028008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame001_links_0000 (interval_append _ 64 128 137 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe5a726b91dc86e4071e38d9c5ce2370eb839bfedf46f7377da96d4269d337197ccaa639b155882b785b8ad9d5daadc560aa354f8a614d5a62128c92348223fd1ee8b0443213d088832407a010fe479e3c81d48e8872e3959c88e3c7173701b50d546a73451a1cce264932318a4c4c6102c595f0ad453629394549f24f527713a89904b224d91d48d645b229111887842c2118e8c7163791a18cac63230517f8bdc5e02c11500a1c4d225e12708f045e22410a080839e1a90b905a42be14109c04b824c10407b03a01ba0d3054028813008303e81cc0c205d02c013809804802300f8078028012007c02400e0048008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 149 :=
  interval_of_check _ 128 21 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 149 record007_frame001_links_0000 (interval_append _ 64 128 149 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xecf761baf1d64eaa74fba21d02e77737b991ca8e4f726391db52d8d6bcb4419e8ce065932a193ebcc5dc2e5d654b1657aab41590abe4fe2749300960495a4812188cd456a1e10da85942220fd06e7ec3f01ea8f447783ba1d4ce9c7343801be0d9c6ca3549a90d146733381998cc465a2e796f4b485692ac9528a5051d28413f89b84cc25e926c92047b23891988c445b22b8f1474c38f1aa0cf06563101810bc05b62b314d8a284de26112788e846422c11208703ca1bc0bb059c2ac13709704902300fa078839c1b60d2054028813008303e81cc0c205d02c013809804802300f8078028012007c02400e0048008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 149 :=
  interval_of_check _ 128 21 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 149 record007_frame002_links_0000 (interval_append _ 64 128 149 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x40880d00e003fe7f6fe5fb3f37e2fb9f5be87ccf8deabcf794ef5dbbb2752e8dcf3826fcde1b2b616b6d3da5b45662c8587aff5e4bc1752db596af95e2b6558aa952296528a194227a4f29cd38a6c4be97529a5249892922a3c4768d519a2e4468790b2043fe7dcf51e83c6784ec1d33966f8de1b736a6c4d79aa350654c517f2d457caa14928c5049d92e2464608690a20a3fc7e0f91e83b8738dc1863045d8ac1542904f092120228420810ee1cc370650c01682984f0941102103e0780d81a0260440740900e01200800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 149 :=
  interval_of_check _ 128 21 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 149 record007_frame003_links_0000 (interval_append _ 64 128 149 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0x3eefb3e9f9fe5f8be0f77dbf67d6f4fd1f3fccefbb8ecfa6e839be478be1b69d975fd3348d0b37ccf2dc670cbeaedb86dfb66c9af2b0abaa8a7a9ca5a88a1a789da6c9ae6598e5e9464f916448fa3c8de2e8b627896208520e81df67c1e9779dc75dd572dc56f9b36c5ac6a9a66919f675895fd7558557535435013b4d5284791442907408fc3e4f63c4eb390da30cc12ecac2a8a4278922408a210811d8711ac62174571444d120421003c0e8340c8260881d0480e0240200400 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 149 :=
  interval_of_check _ 128 21 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 149 record007_frame004_links_0000 (interval_append _ 64 128 149 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0969.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0969.count (({ width := 9, code := 0x10280c01fefe7ebf1f6fa7cbe1eef67abd1e4f1783bddced763add4e873b99cae471b89c2e06d35da8d16833d9ac96331588c2602fd7ab95c2d568b258ac15eae55aa950a75329548a250a813e9e4ca5d2a9248239188b452250c8441200fe7e3e9ecf4793c1cce06e361a4ce6632990c4602e96cb4592c158aa54299449c4b239188a42209007e3c1d8e872381a8d0642e168ac4e2612084401f0f06c34120883c1409038080200 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0969.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 149 :=
  interval_of_check _ 128 21 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0969.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 149 record007_frame005_links_0000 (interval_append _ 64 128 149 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0969
    Papers.RationalityTen.SharedFrameCatalogue.group0969_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x77476f76676276074c74874373873172871e70c6fc6f36ce69168c65d65360f6065e75e05dd5d457056956755d54353751e5034fc4dd4d44b44a549e46945845242b4133df3c33b23a939e39733e33432631f30e2f82e42cc2bd2a829227a26e25d23822221a2091fe1f71ef1e81d61d11c51c01b41a91a119118518017416416015814e14a13f13612912311d11710c1070fe0f60f20e50de0da0cf0c60be0ba08a08908208107e07306905e05a05505204c04b04603b03202702301e01c01501401100b007002001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record008_frame001_links_0000 (interval_append _ 64 128 135 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x1afb5d6b4d5fabb516a1d39a5b47e7eced9c333e58c8b8b715612c1f766e9db3b616bad556dac957aa9536a5541a764e298b2de49c808ed15e24c4384f059f73d878ef11dfbbb70adf5b6b616a2ced903115febc16c2be56aa8d49a875049b930a564989011222242e84cfd9ee3c2750e39c4370670cb1892fe5ecba16e2be554a413d248464838fa1e637c6b8d01822cc558a40f41e43a0730dc19c308560a41342504608a1041c03204e08c0f01c02a0500880b00e00800800 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record008_frame002_links_0000 (interval_append _ 64 128 135 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x10c61642784b0920e41b83304e07c09808ffdfdbf57c6f31e3bb475ce49c6b776e6dc9b734a68ad0d9f33065ac8d8b312608c0576ae65c6b1d5cab253ea3d3ea704ca98d2f25a46e8c91622843a849031fc3e47acf21d93a672cdb9a934463cc39802f45ccb195f2b0554a593f2744b89412523842c841011f23cc748e31b8358690cd1842f45a8ae1542884e89b124234450870e41c43606b0d01902d85209c124230410800f41b83004e08c0f01c02a0500880b00e00800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record008_frame003_links_0000 (interval_append _ 64 128 135 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x74172772271671470a7066ff6f56ed6c56be6b96b069268c68667a65e6516385f55f35da5cb5b759b58556e54a52051b50c50a4eb4e64db4d74bd4b64a048e47945843c42d4254104043fb3c33b739d38c37835b34432a3112ed2df2db2ca2b52ab2a729928a2782672492362102031f41e01d71cb1c21b81b31a91a319919318818217917416d16715b13d12d1181101071021010fc0ed0e70e50df0d70d10cf0c80c50b007907506706306005b05705004e04d04804403603202e02902501f01d01c01200e00a009008007004002001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record009_frame001_links_0000 (interval_append _ 64 128 140 record009_frame001_links_0064 record009_frame001_links_0128))
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x721b709b7ada56cd35e5adcd516a034e99aacc465b32958d8c5b626b0f1836c14603adb96d4b2857b2b4552ca7152528d137a9b54cd264d2b095049aa4b921690647ba335144860420a0b90408013f71f9ce4a71b3689a84cf864030d97fcbe45932bf95e4abe53e2951490a144fa27993a896e494233917489c438217107c8343e61e88ec87403891bd8d4868032918d8c185fc2f013c89344261fa0ea87143761a60bf05d02d815f0a6850c27612e09303a010807e03701a80ce06202f015c0aa054025811406c03201700a404a01f00e807002400e00500240100070020008002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record009_frame002_links_0000 (interval_append _ 64 128 140 record009_frame002_links_0064 record009_frame002_links_0128))
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x322d8cec4d60e30097b8af45632ab54fca6751a27c13d09c64da26a532e96f4ada53127091347f21c506881f3ef1f20f4c79e3cb1e04eea75b3841c04dc46d73641af4d3068733d99a8ca063e2fe17e0bb25d12e116e8b2a58c2bc95c0a8450727493489864a224a120c8c245220c90447e23df1ea8f0c73a38a1be8da869e2e21608ae0526281137892046c2240f5877c39c1c20dc86a032e1860bb058c2a0142099027811807a03481680ae05602a815008604201880bc05a02a013008803e01e00e807003201700a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame001_links_0000 (interval_append _ 64 128 135 record010_frame001_links_0064 record010_frame001_links_0128))
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x34119aacb26363125832b145722b1d508a67520a7f13c69c44d9268d31c95f4a6a4f9252909481a1d10828314009fc4fb87ca3db9df8ed67363721b44d626a13489a04ca06403181880c045fd2de16b4b185832b81594a6e52e28d94409e44ca25212088e645d228911085c4221f20f3476039c1c80df06a033c1980c706062b814609e44b424d11f08804262040ec071c3681a30c906002ec16c0b0053c28a13b097827811807a03481680ae05602a815008604201880bc05a02a013008803e01e00e807003201700a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame002_links_0000 (interval_append _ 64 128 135 record010_frame002_links_0064 record010_frame002_links_0128))
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6c86b56a76916856716065e85df5c85b75a658757f56a55f55855253b5355315265165104c94a849e47f47446646045744e44a43a41440f3fb3f13e93e63d03cd3c63bc3af3a938e38a37637236736434e34b34333f32e3162fe2ec2e42d62ce2c52b62b128a28226f26225b25123e23422f2222161dc1c01b91a519c19117e17416e14a14113512c12511c11510e1060fc0f50ee0e808807e07206305405105004f04e04304203102f02d02a02602201f01e01d01c01901701401000d00a009008007004003002001000 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame003_links_0000 (interval_append _ 64 128 135 record010_frame003_links_0064 record010_frame003_links_0128))
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x16d2d6da6b17606b150da0b3f270cd396b25a4948b90f20a3ec6d8d11922f44c88b051ffbf87bef65e7bcd792ef5dd3af718e21c037b6eedc1ae356698d0995b205fcbe977aec5c4b75632c4578ad54da804e29892c2484828d91221b40c7fcfc9f03d878ce81c73866e4d397e2de59cab14d28c4c89492021841c808fc1f03c4760e71c236c6a8d01962243d8700c41502885009e138218420620bc1682a04c0880f81e03a0700c8170280400680a0120200380400600800800 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame004_links_0000 (interval_append _ 64 128 135 record010_frame004_links_0064 record010_frame004_links_0128))
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0xe21c1b7d6e6da9ad33665ecb18eb17608bc5782ec5ceb95712d95a6b45672c4580a5d442824e09a9312604be9612aa4f46e8d517a2b4508950e216422831009fb3ca78cee1d93a6744e29c13726e0d499831c610bf9772e45acb21602a6540a59442844f49a92c2544908e0fc1e83c4730e31bc34c680cc1822ec5a8b315c2ac540a71482784d0981281cc348650b61382584a092120218420620bc1682a04c0880f81e03a0700c8170280400680a0120200380400600800800 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame005_links_0000 (interval_append _ 64 128 135 record010_frame005_links_0064 record010_frame005_links_0128))
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x11fa3bc728c51762441882101dfc3f27c2f29e23b976aec5d4b9c72ee49c6b7d6f2d59a0b38644c658830d612c11802f95bab6968acc58cb0158aad54ea8549a8f4ee9d53626a4cc9852824e48a90116a1d422810ff1f43d8788eb9cc3706bcd41a133a64cc31822fc5e8b71562905089912e246458889091f23d4778e81c63806d0d61a0324638c217821c3d0700c6158298520a2140218420620bc1682a04c0880f81e03a0700c8170280400680a0120200380400600800800 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame006_links_0000 (interval_append _ 64 128 135 record010_frame006_links_0064 record010_frame006_links_0128))
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x1606bbd6aabb54e9dcf69cf37e664c395b23643c788d518e2e4488810ee1941a824f7de43be748e6dc8b8d714df9be36d690d0d9ab2b648c7d88b0b60abf576ae859eb2d612bf56ead15029d526a3d39a6049e9011d22c44886904a013d6790ed1cd3926fcd91a934e684ca16f2c2568a49422704a08f9192104087d8f61e23b0728e11b6348668c81862243e0740ce1602a8540a6148218420620bc1682a04c0880f81e03a0700c8170280400680a0120200380400600800800 } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record010_frame007_links_0000 (interval_append _ 64 128 135 record010_frame007_links_0064 record010_frame007_links_0128))
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79ea9e59d398a98397696c96095593492b91f9128f08e38a689a88887d86e85f83982c81e80b7dd7cc7507137006c86b569869469068067c66962761f6126095fe5f25d15c85be5b058a57d54c54453652c5215144f14e64dc4ce4a949b4364043f53c73b839c39538837d37936b35e35034332d31e3113032f329528527426625a24823822821a2081f91e91db1b91ad19f19018317216415614613612a11c10b08607907806705805505405305204304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame001_links_0000 (interval_append _ 64 128 145 record011_frame001_links_0064 record011_frame001_links_0128))
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xb925c52e116e4b6a5a7abed5e8ad45632aed55aa8a53f29cd4cea4a51a27bd3d09c44da269d32e96d4ada52927091647f21c506881f3ef1f20f4c79e3cb1e04eea75b3841c04dc46d73641af4d3068733d99a8ca063e2fe97e0bba5d12e316e8b3258c2be95c0aaa542269128892846122910c484441820890047dc3df1e90f0c75a3991c50de46d42f31710b485822b81538a4c50226f12d092046c2240f6877c3a01c20dc86a832e1860bb05942a014209902300f607a03481680ae05602a8150086042018808803e01e00e807003401900c005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame002_links_0000 (interval_append _ 64 128 145 record011_frame002_links_0064 record011_frame002_links_0128))
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x4c297f2f65dcb99672624bc8e9132163f46e8d519a2f45088f0e21bc2d8510960fc0b809001fb3e27aee7dc63856d6d89ac3556a6d45a734664cc958eb1862ac4181afe5f4bd1732de59ab31622be574ad152a9e536a55412784988fd1d22643e85909a0f418820fe1f73e47a0f09d539e728e0197322634c29802f25bcb395e2a4524a013724e4808e116220424808fa1e23946d0d11881b8348680b21302484808e1181f83e05e0880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame003_links_0000 (interval_append _ 64 128 145 record011_frame003_links_0064 record011_frame003_links_0128))
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xbfa5f5af7976aba85c1aca1628af65722b5958ea9654229d94cea48520a7e53c69c14d9268131c95c4a6a4ed25290a481a1d10828314009fc4fb87ca3db9df8ed67363721b44d626a13489a04ca06403181880c045fd2e016b4b205832ba1594a7652e28f94409ee4f224111748a242e211102c7ec3e01e68ef875839c1c60df06bc34c19e0cb06382cd15c0a88518279133896849a23e11688804262040ed071c36c1a30c906082ec16c0b0054428a13b09782300f607a03481680ae05602a8150086042018808803e01e00e807003401900c005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame004_links_0000 (interval_append _ 64 128 145 record011_frame004_links_0064 record011_frame004_links_0128))
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x602bfb7e2f8decbc9712e05b7b676b2d3593b1d622c0d6fad9546a353aa674ae90d0aa093ea794d99a723e35c5c8730aa0e41782702602bfa7aef45e3bc377aed5d139d730e41be3786c4d61a6347686ced94b2463cc6583302598ad15529150e9e93aa6b4c296d29a4c48c8f116a2543e85d081de3a671cde1b435467ccc98e3025ecb916729e5109c92e246464889091fe3d4768e51b61f8388700c6158298520a2140208400620880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame005_links_0000 (interval_append _ 64 128 145 record011_frame005_links_0064 record011_frame005_links_0128))
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x65f65564e64563e63160c6065f25e85e25df5cb5c85c15b75ac5a658657f56855f55655253953552f5265175104c94a849e47f47446646045744e44a43a41440f3fb3f13e93e63d03cd3c63bc3af3a938f38a37937236a36435134b34633f33332e2ec2d62ce2b62b129f29228928227826b26225825124623b23422b2221ec1dc1d01c01b91af1a519c19118817e17416e14b14113612c12511e11510e1060fe0f50ee0e807e07307206305405105004f04e04304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame006_links_0000 (interval_append _ 64 128 145 record011_frame006_links_0064 record011_frame006_links_0128))
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x41c83105208c0f810fddfabee7d0f95f23df7b8f6dea3c8786ed5d93a873ee6dcbb8b710e11beb6d6cecb98b30c5eabb9722e05b8b5d6aacc56eacd55aa4540a7d4ca95528a3d4127d4e49c1362654c297d2ba534a293520a3d4247fcfb9e43be750e69c33786e4d99ac34e688cd99431e628c31632b053ca41402744c497124238454869091ee3c0750e41be364698d019430c5f0b91681d03586a0be1402684c096128208400620880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame007_links_0000 (interval_append _ 64 128 145 record011_frame007_links_0064 record011_frame007_links_0128))
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xce166732fd91cc7861d2e8d722b6b5ac2d21670aff576ab6958ca9a54328dd44a9ff4f627713989934c0a5b92b492e48d232d16c8af44d224d10286c42c208d01c7d83a69cf0e3070937c9ba4d6c6a53499a0ccb86492fc179cb865b42d21650ac255029f14b8a0e4f42529240912476238116c88842c20c100c7d03d11dd0e986fe3681aa8cfc6542a814c0a244f226b12d092c47822d10e08344001f20e286d434c1960c405dc2d01590a504e425411d08782300f607a03481680ae05602a8150086042018808803e01e00e807003401900c005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame008_links_0000 (interval_append _ 64 128 145 record011_frame008_links_0064 record011_frame008_links_0128))
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x64564364163c63a63260b6075fa5f55ec5e55cb5c55bf5b459c59256f56955d55755154853052952151a5014f54bb4a94a249048a47f47c47747146c46143643042441d41540b3f43ed3e83de3c73bb39538f38237d37536b35334e34533e32531c2e02cd2c62b72b32a72a229928f28927e27326725a24923e23122521b1d41cb1c31b81b11a319819118617b17216815f14513d13312b12111410b1010f60ec0e40d80cf08207707606605805505405305204104003002201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame009_links_0000 (interval_append _ 64 128 145 record011_frame009_links_0064 record011_frame009_links_0128))
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x75174b74773a7367216e86e26cb6c16b96b069668a68067766265262d6276116086005f65dc5d35cb5bf5a759755954653f52a52351750e5074f44eb4d448f48947046745c45543942f4234184003ef3c23bc3a439d39438b36e36335834e3333222e42d12ca2b72b12a229728e28727d27026325924c23c23022221820a1c21bb1b41ad1a81a019618f18617b16f16916014213b13412d12812011610d1070fb0ef0e70e208a07b07a06905a05705605505404304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame010_links_0000 (interval_append _ 64 128 145 record011_frame010_links_0064 record011_frame010_links_0128))
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
def record011_frame011_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x3f27e0fbdf63e97c8f39e6bc377aee9daba873ce65ca3856fcdb5b5b616bad65aa347684cf19b325636be173ae25a2b31622bf57aae1592a551ca2940a7b4f09cd33a5e4b294d22a3f4588a90f21a42c849022003f27d0f29dc3726a4d219432061cc197d2f05d4b816c2d058caf95629e5209f92323a4688a91321e428831011f63d0788e71b2354690d0196320610bd1742cc568a61441b0338660b21382584a0921201d83a05a0880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record011) (record011.maps 11)
      (record011.inverseMaps 11) record011_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame011_links_0000 (interval_append _ 64 128 145 record011_frame011_links_0064 record011_frame011_links_0128))
theorem record011_frame011_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 11 :=
  of_group record011 11 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record011_frame011_indices record011_frame011_graph record011_frame011_links
def record011_frame012_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7ac7a77a278b78677073772c7167086fb6f26d16c86c26b96a469d67966e65b65264c6436226146075fe5e65df5ad59859157c57556b56155653752c5104d54c74b14a749c49046f46645c45243843140c3fe3ec3e33d93cf3a939f39438836f36833732231c3073012f62ee2e12d82cc2b92ab29c28e2742612532442361f81ea1de1d11c61bb1b21ac1a319718f18717e16215414813b13012411c11410b1020f90f30ea08c07b07a06905a05705605505404304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 12)
      (record011.inverseMaps 12) record011_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame012_links_0000 (interval_append _ 64 128 145 record011_frame012_links_0064 record011_frame012_links_0128))
theorem record011_frame012_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 12 :=
  of_group record011 12 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record011_frame012_indices record011_frame012_graph record011_frame012_links
def record011_frame013_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x48b91121a3e47a8d912a2243a8690c215c1d82f04e06c027f8f9df0bd579ef2de2bb8766ec1d539f732dc9b135b690d099cb31652c718bb055b6b5d652c457eaf1552a5540a6945a854d699d2ba514949151a23145a89d0da153d8770eb1c337c6c8d59a533e66cc998c30c600bc9712d6598af93f2744d09792b24e4889011c22a43c859061ee3c8768e81c83786c0d419e328628c217e1f8388700c4158298520a2140208400600880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record011) (record011.maps 13)
      (record011.inverseMaps 13) record011_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame013_links_0000 (interval_append _ 64 128 145 record011_frame013_links_0064 record011_frame013_links_0128))
theorem record011_frame013_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 13 :=
  of_group record011 13 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record011_frame013_indices record011_frame013_graph record011_frame013_links
def record011_frame014_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0246.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0246.count (({ width := 9, code := 0x160af576b95bad55aab53a8d3e9b4ba55228d45a1d06813f9ecee75389bcd6673097ca64f2591c8a3f1d8e46e35198ac52251087432150983c160902803fdfcfc7d3e5eef67a3c9deee74399c8e270b71b0d367b3590c460afd76b85b2c95a9f4ea652c9448a3918894320d027e3b1c8de6b34998c65f2e168b05529900763a1a8c05e2e168b04e2610870361a0c8602c150a04c22100703416090401c0c04018080200 } : Fields).get c.val)
theorem record011_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record011) (record011.maps 14)
      (record011.inverseMaps 14) record011_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame014_links_0000 (interval_append _ 64 128 145 record011_frame014_links_0064 record011_frame014_links_0128))
theorem record011_frame014_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 14 :=
  of_group record011 14 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0246
    Papers.RationalityTen.SharedFrameCatalogue.group0246_facts record011_frame014_indices record011_frame014_graph record011_frame014_links
def record011_frame015_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0144.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0144.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0144.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0144.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0144.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0144.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0144.localPairCheck (smallEmbedding record011) (record011.maps 15)
      (record011.inverseMaps 15) record011_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame015_links_0000 (interval_append _ 64 128 145 record011_frame015_links_0064 record011_frame015_links_0128))
theorem record011_frame015_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 15 :=
  of_group record011 15 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0144
    Papers.RationalityTen.SharedFrameCatalogue.group0144_facts record011_frame015_indices record011_frame015_graph record011_frame015_links
def record011_frame016_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0225.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0225.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0225.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0225.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0225.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0225.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0225.localPairCheck (smallEmbedding record011) (record011.maps 16)
      (record011.inverseMaps 16) record011_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame016_links_0000 (interval_append _ 64 128 145 record011_frame016_links_0064 record011_frame016_links_0128))
theorem record011_frame016_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 16 :=
  of_group record011 16 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0225
    Papers.RationalityTen.SharedFrameCatalogue.group0225_facts record011_frame016_indices record011_frame016_graph record011_frame016_links
def record011_frame017_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0240.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0240.count (({ width := 8, code := 0xd4d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0aeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8a8784817f7c7a787674716f6d6b676563615f5c5a58565452504e4b49474543403e3c3a383634322a2726242221201f1e1b1a18161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0240.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record011) (record011.maps 17)
      (record011.inverseMaps 17) record011_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame017_links_0000 (interval_append _ 64 128 145 record011_frame017_links_0064 record011_frame017_links_0128))
theorem record011_frame017_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 17 :=
  of_group record011 17 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0240
    Papers.RationalityTen.SharedFrameCatalogue.group0240_facts record011_frame017_indices record011_frame017_graph record011_frame017_links
def record011_frame018_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0140.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0140.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0140.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0140.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0140.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0140.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0140.localPairCheck (smallEmbedding record011) (record011.maps 18)
      (record011.inverseMaps 18) record011_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame018_links_0000 (interval_append _ 64 128 145 record011_frame018_links_0064 record011_frame018_links_0128))
theorem record011_frame018_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 18 :=
  of_group record011 18 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0140
    Papers.RationalityTen.SharedFrameCatalogue.group0140_facts record011_frame018_indices record011_frame018_graph record011_frame018_links
def record011_frame019_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0222.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0222.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0222.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0222.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0222.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0222.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0222.localPairCheck (smallEmbedding record011) (record011.maps 19)
      (record011.inverseMaps 19) record011_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame019_links_0000 (interval_append _ 64 128 145 record011_frame019_links_0064 record011_frame019_links_0128))
theorem record011_frame019_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 19 :=
  of_group record011 19 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0222
    Papers.RationalityTen.SharedFrameCatalogue.group0222_facts record011_frame019_indices record011_frame019_graph record011_frame019_links
def record011_frame020_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0119.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0119.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0119.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record011) (record011.maps 20)
      (record011.inverseMaps 20) record011_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame020_links_0000 (interval_append _ 64 128 145 record011_frame020_links_0064 record011_frame020_links_0128))
theorem record011_frame020_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 20 :=
  of_group record011 20 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0119
    Papers.RationalityTen.SharedFrameCatalogue.group0119_facts record011_frame020_indices record011_frame020_graph record011_frame020_links
def record011_frame021_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0244.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0244.count (({ width := 8, code := 0xc0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b79777573716f6d6b69676563615f5b59575553514f4d4b49474543403e3c3a38363432302e2c2a282221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0244.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record011) (record011.maps 21)
      (record011.inverseMaps 21) record011_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame021_links_0000 (interval_append _ 64 128 145 record011_frame021_links_0064 record011_frame021_links_0128))
theorem record011_frame021_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 21 :=
  of_group record011 21 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0244
    Papers.RationalityTen.SharedFrameCatalogue.group0244_facts record011_frame021_indices record011_frame021_graph record011_frame021_links
def record011_frame022_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0223.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0223.count (({ width := 9, code := 0x10883c1a0b0481bf5f8f97bbd5e6ef76badd2e773395c8e16fb75b6d76ab4da2cf673218ec662b1186c260b017ebe5c2dd68b2582b954a85329144a15027d389a4c259249047231148941a0902803f9f8fa7c3d9e8f0763a1c8e06e361a8d06431180bc5d2e168b0562a148a04e251208c4421908803e1e0e870361a0c86230168b05228138984a24108803a1c0d86832180b8582a14088401a0a048200e04018080200 } : Fields).get c.val)
theorem record011_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0223.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record011) (record011.maps 22)
      (record011.inverseMaps 22) record011_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame022_links_0000 (interval_append _ 64 128 145 record011_frame022_links_0064 record011_frame022_links_0128))
theorem record011_frame022_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 22 :=
  of_group record011 22 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0223
    Papers.RationalityTen.SharedFrameCatalogue.group0223_facts record011_frame022_indices record011_frame022_graph record011_frame022_links
def record011_frame023_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0120.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0120.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0120.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0120.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0120.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0120.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0120.localPairCheck (smallEmbedding record011) (record011.maps 23)
      (record011.inverseMaps 23) record011_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame023_links_0000 (interval_append _ 64 128 145 record011_frame023_links_0064 record011_frame023_links_0128))
theorem record011_frame023_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 23 :=
  of_group record011 23 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0120
    Papers.RationalityTen.SharedFrameCatalogue.group0120_facts record011_frame023_indices record011_frame023_graph record011_frame023_links
def record011_frame024_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0238.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0238.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0238.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0238.localPairCheck (smallEmbedding record011) (record011.maps 24) (record011.inverseMaps 24) record011_frame024_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0238.localPairCheck (smallEmbedding record011) (record011.maps 24) (record011.inverseMaps 24) record011_frame024_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0238.localPairCheck (smallEmbedding record011) (record011.maps 24) (record011.inverseMaps 24) record011_frame024_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0238.localPairCheck (smallEmbedding record011) (record011.maps 24)
      (record011.inverseMaps 24) record011_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame024_links_0000 (interval_append _ 64 128 145 record011_frame024_links_0064 record011_frame024_links_0128))
theorem record011_frame024_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 24 :=
  of_group record011 24 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0238
    Papers.RationalityTen.SharedFrameCatalogue.group0238_facts record011_frame024_indices record011_frame024_graph record011_frame024_links
def record011_frame025_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcb8651b2458b2c46603ad9d6a8b2c58b2c115e2ab354faa2d4eca4a51aa7713949a44c9a6012da93449024391f88d145f20c0ff67e93db9e9cf0876f3ae9c94e246d33199880bf05e22e816f4afe56b2ab9508a2c50125412588e045f22610e48003ec1ed0f2073a38a17e0b1c56a283139895449c24511f08e4460229111086c41e2060ff87e03e21c10dd06cc3581a60cf065c32218a0c105ec2ea16e0ac054429414309e84d425c128090846422410c08282300f607a03481680ae05602a8150086042018808803e01e00e807003401900c005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record011_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 25) (record011.inverseMaps 25) record011_frame025_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 25) (record011.inverseMaps 25) record011_frame025_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 25) (record011.inverseMaps 25) record011_frame025_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 25)
      (record011.inverseMaps 25) record011_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame025_links_0000 (interval_append _ 64 128 145 record011_frame025_links_0064 record011_frame025_links_0128))
theorem record011_frame025_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 25 :=
  of_group record011 25 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame025_indices record011_frame025_graph record011_frame025_links
def record011_frame026_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x62d62a62661c61860d5da5d55cb5c15bb5b159b59058a57d56955c5395315245185115064ee4e44e04d44bc4ae46543c4304104073f43f13ed3e33df3d43a239d39038c38237c36035b34f34932e3252ff2fa2ea2e32d72cf2b32ae2a429e28227722c2031f71d71ce1bb1b91b51b01ac1a61a019a19418b18517f17a17515314e14814213d13713112d12912411e1181131091040ff0fa0f60ef0e90e50e00d90d30cf0c907e07307206205305004f04e04d04204103102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 26) (record011.inverseMaps 26) record011_frame026_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 26) (record011.inverseMaps 26) record011_frame026_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 26) (record011.inverseMaps 26) record011_frame026_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record011) (record011.maps 26)
      (record011.inverseMaps 26) record011_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame026_links_0000 (interval_append _ 64 128 145 record011_frame026_links_0064 record011_frame026_links_0128))
theorem record011_frame026_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 26 :=
  of_group record011 26 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record011_frame026_indices record011_frame026_graph record011_frame026_links
def record011_frame027_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x69769368b68167b66863563061e61460a6005ea5e35da5d25c05b458d58757456b56255954653f53352c51950d4c94a749a47b46f45d45745444644242e3fb3f63e33d93d23c83af3a73a139a38637a35334d33933032a32130a3032fb2f42df2d328f26a25f23e23422121921220e2091ff1f81f01e91e11d71ce1c61bd18f18717e17617016b16515f15714e14914213912712111b11511010c1071010f90f20ed0e80e108807907806705805505405305204304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 27) (record011.inverseMaps 27) record011_frame027_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 27) (record011.inverseMaps 27) record011_frame027_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 27) (record011.inverseMaps 27) record011_frame027_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 27)
      (record011.inverseMaps 27) record011_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame027_links_0000 (interval_append _ 64 128 145 record011_frame027_links_0064 record011_frame027_links_0128))
theorem record011_frame027_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 27 :=
  of_group record011 27 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record011_frame027_indices record011_frame027_graph record011_frame027_links
def record011_frame028_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6cd6c26bb6a169b68465164763462b62261c5fb5f25e95e25cc5c65a459858457c57456e54f54753e53752051a4d34ba4b249448a47d47146b45344c4344013f73e23d93d03c93a839f39639037c3763543483313293203192fa2f22ea2e42d02ca28326425a24123922b22421b21520f2041fb1f41ec1de1d31ca1c31bb19719018918217d17416c16415b15114914113812812211d11811310b1050ff0f90f10eb0e50df08c07b07a06905a05705605505404304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record011) (record011.maps 28) (record011.inverseMaps 28) record011_frame028_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record011) (record011.maps 28) (record011.inverseMaps 28) record011_frame028_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record011) (record011.maps 28) (record011.inverseMaps 28) record011_frame028_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record011) (record011.maps 28)
      (record011.inverseMaps 28) record011_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame028_links_0000 (interval_append _ 64 128 145 record011_frame028_links_0064 record011_frame028_links_0128))
theorem record011_frame028_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 28 :=
  of_group record011 28 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record011_frame028_indices record011_frame028_graph record011_frame028_links
def record011_frame029_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x4b595f2b251c9f92f1e639c6b8c91862cc4a8830f61a426845036023fc7ecfcdf73e17b2f4de5bb9766e1dbab6d6acd35a1b3c670cc196b2560cc0d7b2f15d0b9568acd58cb115a2b0532a51442834f89d931a5f4b295d2324142a7fcfb1e33b6744e69c73806e8d91ac34e684cb18f31260cbe95c2ac540a59472824e49a12d24a47c8c91220e4087e0f61e23a4708dc1ac334638c11761f03806f0c01482784e09a1302003f0600880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 29) (record011.inverseMaps 29) record011_frame029_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 29) (record011.inverseMaps 29) record011_frame029_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 29) (record011.inverseMaps 29) record011_frame029_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record011) (record011.maps 29)
      (record011.inverseMaps 29) record011_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame029_links_0000 (interval_append _ 64 128 145 record011_frame029_links_0064 record011_frame029_links_0128))
theorem record011_frame029_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 29 :=
  of_group record011 29 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record011_frame029_indices record011_frame029_graph record011_frame029_links
def record011_frame030_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x46a8cb1862ec5989f0c61642383905a09404800fe9f9be87c4f39e53c0774ed1d8ba273ee6dca387704d85a934d676cd995b26646c758cb105e4bb570ada5aab45612be574acd54aa351ea2d3f2774e09b52fa5c4b294d24243444845051fa3ec7acf21de3b4754e51c23766d4d61a333a654c69662ba558a69492844e49912924045c881091ec3c4760e71c83786c0d319a318600bb16c1e83806f0c01442704d09812c208400620880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 30) (record011.inverseMaps 30) record011_frame030_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 30) (record011.inverseMaps 30) record011_frame030_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 30) (record011.inverseMaps 30) record011_frame030_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record011) (record011.maps 30)
      (record011.inverseMaps 30) record011_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame030_links_0000 (interval_append _ 64 128 145 record011_frame030_links_0064 record011_frame030_links_0128))
theorem record011_frame030_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 30 :=
  of_group record011 30 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record011_frame030_indices record011_frame030_graph record011_frame030_links
def record011_frame031_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x549a894fe9c532a4741e80cfb9e53ba73cda9a3336604af953252474868ff1ea39c678bf16a2843f871011f9beb7a4f21ddbb375ee91d13956eedd5b1b5b6a8d419f33a66acc99031a608c01792ea5c6b79662c8588b0157aa94ec9712923e4708a910214416814fd9f03d4788eb1cd38c6f4db1842f65ccb59652c055ca81452784d495922224428820fe1f03cc768ea1c636c6b0d1196200398720c61502885009e138208400620880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record011) (record011.maps 31) (record011.inverseMaps 31) record011_frame031_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record011) (record011.maps 31) (record011.inverseMaps 31) record011_frame031_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record011) (record011.maps 31) (record011.inverseMaps 31) record011_frame031_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record011) (record011.maps 31)
      (record011.inverseMaps 31) record011_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame031_links_0000 (interval_append _ 64 128 145 record011_frame031_links_0064 record011_frame031_links_0128))
theorem record011_frame031_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 31 :=
  of_group record011 31 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record011_frame031_indices record011_frame031_graph record011_frame031_links
def record011_frame032_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8027f97f17e27de7c477576a75074573a7307107066f96ef6d16c568a67e65f65264763b61860d5ff5f35d05c256e55554c53452c51f51650e4ff4fb4e149048446545844d44141e4134053f93d63c838737c36235734c34232231830b3012e32d728b27226925124923c23522c22522021821120b2051fa1f11ea1e41dd1af1a71a019819018718017917116816115b15313d13512e12611e11510e1070ff0f60ef0e90e108c07b07a06905a05705605505404304203102201f01e01d01c01a01901801701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record011_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 32) (record011.inverseMaps 32) record011_frame032_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 32) (record011.inverseMaps 32) record011_frame032_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 32) (record011.inverseMaps 32) record011_frame032_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 32)
      (record011.inverseMaps 32) record011_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame032_links_0000 (interval_append _ 64 128 145 record011_frame032_links_0064 record011_frame032_links_0128))
theorem record011_frame032_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 32 :=
  of_group record011 32 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record011_frame032_indices record011_frame032_graph record011_frame032_links
def record011_frame033_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x4879071fa3bc738cf1522944587d0de18c2584106a0a408802fb5f53da7a6f31e33b8764eb1d2b9571ad65a233c658c998cb14622c21832f95ccb8d69acd58cafd582a954aa7d472864d89a92e2564a492d1ea374688bd102193d6754e71bd36e6acd299f338668cb19131c624c197c2ec5c0b514c28e5089f13a26a4bc9512223645c8990d1f43d8788ec1ce3886e0d619e320620bf1741d8348680b413c2604b0941241e03b05c0880f81e03a0700d01903005c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record011_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record011) (record011.maps 33) (record011.inverseMaps 33) record011_frame033_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record011) (record011.maps 33) (record011.inverseMaps 33) record011_frame033_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame033_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record011) (record011.maps 33) (record011.inverseMaps 33) record011_frame033_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record011) (record011.maps 33)
      (record011.inverseMaps 33) record011_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame033_links_0000 (interval_append _ 64 128 145 record011_frame033_links_0064 record011_frame033_links_0128))
theorem record011_frame033_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 33 :=
  of_group record011 33 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record011_frame033_indices record011_frame033_graph record011_frame033_links
def record011_frame034_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1074.count (({ width := 10, code := 0x38ce2788e1383dfb67d935bd5f53d4747d1341d0336ccf23c8316c4b0ec32fdbe6f5bcee7b8ebaab6a7a6692a1e84a0e7f9fa799865e952509324a8ee378ce318962183a0b816027fdfe7c5ed7a5e7775da6d5aa68d93635826017c5e5765c16b59d63571565454d525304a5244811c45d1143508400fb3dcf2380d9350d0330c7308be2e4b02a8a62846817c5e140481144410c420e4380b82207c1e0741c068190601705414044100340a0240801c0400c0200400 } : Fields).get c.val)
theorem record011_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record011) (record011.maps 34) (record011.inverseMaps 34) record011_frame034_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record011) (record011.maps 34) (record011.inverseMaps 34) record011_frame034_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame034_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record011) (record011.maps 34) (record011.inverseMaps 34) record011_frame034_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record011) (record011.maps 34)
      (record011.inverseMaps 34) record011_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame034_links_0000 (interval_append _ 64 128 145 record011_frame034_links_0064 record011_frame034_links_0128))
theorem record011_frame034_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 34 :=
  of_group record011 34 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1074
    Papers.RationalityTen.SharedFrameCatalogue.group1074_facts record011_frame034_indices record011_frame034_graph record011_frame034_links
def record011_frame035_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x1f47c5f07bded7b1e5791e0771da75dd2745ce729c8715c3709bd6e9b86d9b26c5ae6ada66919764d9163d8c621866158460d825d9755c96f5b169591635815d56156551525414d52d4850d414fd3c4dd344b129495224851b461144450f42504404fe3e8f63d0ef3a4d4348cd324c730cbe2ecb62c8ad2a8a626c9624c8e230882107e1e4761cc6e1ac4810c420f0360cc320c4300ac2a0881c06c1a064180581505013044100380d02c09020070180400c0200400 } : Fields).get c.val)
theorem record011_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record011) (record011.maps 35) (record011.inverseMaps 35) record011_frame035_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record011) (record011.maps 35) (record011.inverseMaps 35) record011_frame035_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame035_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record011) (record011.maps 35) (record011.inverseMaps 35) record011_frame035_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record011) (record011.maps 35)
      (record011.inverseMaps 35) record011_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame035_links_0000 (interval_append _ 64 128 145 record011_frame035_links_0064 record011_frame035_links_0128))
theorem record011_frame035_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 35 :=
  of_group record011 35 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record011_frame035_indices record011_frame035_graph record011_frame035_links
def record011_frame036_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0143.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0143.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0143.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0143.localPairCheck (smallEmbedding record011) (record011.maps 36) (record011.inverseMaps 36) record011_frame036_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0143.localPairCheck (smallEmbedding record011) (record011.maps 36) (record011.inverseMaps 36) record011_frame036_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame036_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0143.localPairCheck (smallEmbedding record011) (record011.maps 36) (record011.inverseMaps 36) record011_frame036_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0143.localPairCheck (smallEmbedding record011) (record011.maps 36)
      (record011.inverseMaps 36) record011_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame036_links_0000 (interval_append _ 64 128 145 record011_frame036_links_0064 record011_frame036_links_0128))
theorem record011_frame036_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 36 :=
  of_group record011 36 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0143
    Papers.RationalityTen.SharedFrameCatalogue.group0143_facts record011_frame036_indices record011_frame036_graph record011_frame036_links
def record011_frame037_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0224.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0224.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0224.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0224.localPairCheck (smallEmbedding record011) (record011.maps 37) (record011.inverseMaps 37) record011_frame037_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0224.localPairCheck (smallEmbedding record011) (record011.maps 37) (record011.inverseMaps 37) record011_frame037_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame037_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0224.localPairCheck (smallEmbedding record011) (record011.maps 37) (record011.inverseMaps 37) record011_frame037_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0224.localPairCheck (smallEmbedding record011) (record011.maps 37)
      (record011.inverseMaps 37) record011_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame037_links_0000 (interval_append _ 64 128 145 record011_frame037_links_0064 record011_frame037_links_0128))
theorem record011_frame037_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 37 :=
  of_group record011 37 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0224
    Papers.RationalityTen.SharedFrameCatalogue.group0224_facts record011_frame037_indices record011_frame037_graph record011_frame037_links
def record011_frame038_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0239.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0239.count (({ width := 8, code := 0xa2a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a5855535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2c29282624232221201d1c1a18171615141211100f0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0239.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record011) (record011.maps 38) (record011.inverseMaps 38) record011_frame038_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record011) (record011.maps 38) (record011.inverseMaps 38) record011_frame038_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame038_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record011) (record011.maps 38) (record011.inverseMaps 38) record011_frame038_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record011) (record011.maps 38)
      (record011.inverseMaps 38) record011_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame038_links_0000 (interval_append _ 64 128 145 record011_frame038_links_0064 record011_frame038_links_0128))
theorem record011_frame038_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 38 :=
  of_group record011 38 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0239
    Papers.RationalityTen.SharedFrameCatalogue.group0239_facts record011_frame038_indices record011_frame038_graph record011_frame038_links
def record011_frame039_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0139.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0139.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0139.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0139.localPairCheck (smallEmbedding record011) (record011.maps 39) (record011.inverseMaps 39) record011_frame039_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0139.localPairCheck (smallEmbedding record011) (record011.maps 39) (record011.inverseMaps 39) record011_frame039_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame039_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0139.localPairCheck (smallEmbedding record011) (record011.maps 39) (record011.inverseMaps 39) record011_frame039_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0139.localPairCheck (smallEmbedding record011) (record011.maps 39)
      (record011.inverseMaps 39) record011_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame039_links_0000 (interval_append _ 64 128 145 record011_frame039_links_0064 record011_frame039_links_0128))
theorem record011_frame039_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 39 :=
  of_group record011 39 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0139
    Papers.RationalityTen.SharedFrameCatalogue.group0139_facts record011_frame039_indices record011_frame039_graph record011_frame039_links
def record011_frame040_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0221.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0221.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0221.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0221.localPairCheck (smallEmbedding record011) (record011.maps 40) (record011.inverseMaps 40) record011_frame040_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0221.localPairCheck (smallEmbedding record011) (record011.maps 40) (record011.inverseMaps 40) record011_frame040_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame040_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0221.localPairCheck (smallEmbedding record011) (record011.maps 40) (record011.inverseMaps 40) record011_frame040_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0221.localPairCheck (smallEmbedding record011) (record011.maps 40)
      (record011.inverseMaps 40) record011_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame040_links_0000 (interval_append _ 64 128 145 record011_frame040_links_0064 record011_frame040_links_0128))
theorem record011_frame040_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 40 :=
  of_group record011 40 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0221
    Papers.RationalityTen.SharedFrameCatalogue.group0221_facts record011_frame040_indices record011_frame040_graph record011_frame040_links
def record011_frame041_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0243.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0243.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0243.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0243.localPairCheck (smallEmbedding record011) (record011.maps 41) (record011.inverseMaps 41) record011_frame041_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0243.localPairCheck (smallEmbedding record011) (record011.maps 41) (record011.inverseMaps 41) record011_frame041_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame041_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0243.localPairCheck (smallEmbedding record011) (record011.maps 41) (record011.inverseMaps 41) record011_frame041_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0243.localPairCheck (smallEmbedding record011) (record011.maps 41)
      (record011.inverseMaps 41) record011_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame041_links_0000 (interval_append _ 64 128 145 record011_frame041_links_0064 record011_frame041_links_0128))
theorem record011_frame041_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 41 :=
  of_group record011 41 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0243
    Papers.RationalityTen.SharedFrameCatalogue.group0243_facts record011_frame041_indices record011_frame041_graph record011_frame041_links
def record011_frame042_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0141.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0141.count (({ width := 8, code := 0x908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0141.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0141.localPairCheck (smallEmbedding record011) (record011.maps 42) (record011.inverseMaps 42) record011_frame042_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0141.localPairCheck (smallEmbedding record011) (record011.maps 42) (record011.inverseMaps 42) record011_frame042_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame042_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0141.localPairCheck (smallEmbedding record011) (record011.maps 42) (record011.inverseMaps 42) record011_frame042_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0141.localPairCheck (smallEmbedding record011) (record011.maps 42)
      (record011.inverseMaps 42) record011_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame042_links_0000 (interval_append _ 64 128 145 record011_frame042_links_0064 record011_frame042_links_0128))
theorem record011_frame042_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 42 :=
  of_group record011 42 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0141
    Papers.RationalityTen.SharedFrameCatalogue.group0141_facts record011_frame042_indices record011_frame042_graph record011_frame042_links
def record011_frame043_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0237.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0237.count (({ width := 8, code := 0xa2a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a5855535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2c29282624232221201d1c1a18171615141211100f0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0237.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record011) (record011.maps 43) (record011.inverseMaps 43) record011_frame043_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record011) (record011.maps 43) (record011.inverseMaps 43) record011_frame043_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame043_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record011) (record011.maps 43) (record011.inverseMaps 43) record011_frame043_indices (Fin.ofNat record011.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record011_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record011) (record011.maps 43)
      (record011.inverseMaps 43) record011_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record011_frame043_links_0000 (interval_append _ 64 128 145 record011_frame043_links_0064 record011_frame043_links_0128))
theorem record011_frame043_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 43 :=
  of_group record011 43 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0237
    Papers.RationalityTen.SharedFrameCatalogue.group0237_facts record011_frame043_indices record011_frame043_graph record011_frame043_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (Fin.cases (record011_frame011_supported hcells) (Fin.cases (record011_frame012_supported hcells) (Fin.cases (record011_frame013_supported hcells) (Fin.cases (record011_frame014_supported hcells) (Fin.cases (record011_frame015_supported hcells) (Fin.cases (record011_frame016_supported hcells) (Fin.cases (record011_frame017_supported hcells) (Fin.cases (record011_frame018_supported hcells) (Fin.cases (record011_frame019_supported hcells) (Fin.cases (record011_frame020_supported hcells) (Fin.cases (record011_frame021_supported hcells) (Fin.cases (record011_frame022_supported hcells) (Fin.cases (record011_frame023_supported hcells) (Fin.cases (record011_frame024_supported hcells) (Fin.cases (record011_frame025_supported hcells) (Fin.cases (record011_frame026_supported hcells) (Fin.cases (record011_frame027_supported hcells) (Fin.cases (record011_frame028_supported hcells) (Fin.cases (record011_frame029_supported hcells) (Fin.cases (record011_frame030_supported hcells) (Fin.cases (record011_frame031_supported hcells) (Fin.cases (record011_frame032_supported hcells) (Fin.cases (record011_frame033_supported hcells) (Fin.cases (record011_frame034_supported hcells) (Fin.cases (record011_frame035_supported hcells) (Fin.cases (record011_frame036_supported hcells) (Fin.cases (record011_frame037_supported hcells) (Fin.cases (record011_frame038_supported hcells) (Fin.cases (record011_frame039_supported hcells) (Fin.cases (record011_frame040_supported hcells) (Fin.cases (record011_frame041_supported hcells) (Fin.cases (record011_frame042_supported hcells) (Fin.cases (record011_frame043_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))
#print axioms record011_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091
