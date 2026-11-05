module
prelude
public import GraphInputsRow29Part00105Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups042Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups080Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb4bb3fb33ab7ab2a6fa62a40a3397c9729259188f78ea7126b46a269869369068067b66a63362f61960e6055d85b85aa58b57e54c5445325285215144f14e64d74c94ae4a046f4624544464224124033e33d53b73a838c38136a35d3543473223153022f22db2cf2982882772692462362272061f71da1cd18314611c0fe0db0ce05e05905305204e04d04604503903803503402802301d01c01300e008007004003002001000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3cf5e20eea6ab350d980cab63f31ad5e2ade52da919432a06482a3891b88d445ea2b90fc8684191efcf587753ae1d28df26bc35419fccd460a2fc973cb7a5ae2cd958caa253a294141c9ec4ae24e12288f245222010c481e3ff1f00f4473638a1b00d3867e32c17a0b885962b914c0a1c47e22d10d88283c61d10e106803201710b104cc22e10407b038c1ba06002d81540a804e026811808a03901c00d40680280118074038013007002000e0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x9b32c25043686507e0bc1580aff5ebbcd78aeb1d43a2734e21bf36a6c2d45a0b3c58cb05562a5544a3943a5949891514a2443c85d019f83ca76ce69bd37067cc016b2a44e89110f216414810e81b034c678c51762b85509911c218410790e619c2b8510a0124218360460740e01902e0500981001c0280400700600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7063551a1eb24588aad953ea9152928e93549834b6a4191ee8d9461a1f50ae8193fc1f4cf4c7952f81774b0456b2ae9478a0c47622790e47a43c31d28e3c6923231728b1053e27213088f84361ff0ee06e832e17b0ba85b42ce143097049c24211207f03a01c40bd050825012008503e81bc0b605502a013408a037011807403801900b805002601000700280100070018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0xd5347cfb01bfef3bc2efb92e0b32c7b12aeaaea1a728aa0a769c6649625086e18812017fdf17b1d5745ce6f5bb6d5b16959e6418a5f5715a95c521374910b3d4e437cdc358bf2ccb02a09f24889210731b4661905f16c51118400fc3d0e02f08c1d0701905c1404c100380a0200700c0200400 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x14ee91d18a2b2e24ec8e8f713e20c1981ef35d5ba6748e75cc38b70cddd99315624c217aaf1584afd5a299514a05362674b094926a404788c51621a4267fcfb9f33d2750e61c136c6acd09812ec57ca09352564948a1021d83906e8cd1762a45108f1181b42d8550a81382684608a0f81c83706a0b0148250460740e01301c0280400700600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
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
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7076c869968267966a66262261c6005d05ca5bd5a259b58c58154854051f5054f04e14c84b749848a47d47747146c42641d3ff3cc3c33b339c39538737d33b33531d3082f92ec2d92ca2b12a829e29a29729427324f2182021f31d51c019518617d16616213c11d0e60dc0c00ba09f09809308d08907e06905d05905305204a03302702301d01c01a01801501200f00e00a008007003002001000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3ed1d3cdc86b4b4f19eeccc61ab085778b2c58cabdd52ea7c51ea8492f696549323d118c898435a11d00e7e83e11ed0f4c7953809bb4d105f82f2970cac6548284937888e4311f90f0072436419b8c4c5a62b41470a004e426112288c040e1f90f6073838219e0c886242da1670a504d42160fe074038816c0a6050024c11e084035817c0b605502a0130066027011807403801a00c005402400f00700280100070018008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3789b06d56687ac1d5e2ab954729d94a4a3a4efa72934e9934c1a5b525891b488a3f11b28c343da1310327e93e99ed8f4e7952e996f4b0a55a2a11478a0c4ab24b11cc8be44f21c8fe07ce3dd1e40e9471e34718c0b9456a29f14109cc4c223e114886c3e21dc0d6065c31417b0ba05b82ce1510a184f425c128090844820a0fe074828c12e09404801fc0b805602a815008e02400f007403801900b805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x300d79ebad5bca99d4c0a3f509a8053c69d14c5a5ed2ca9554a725192248fc47823751728a643120b4ff27d23dd9e44efe76d3301964c6e60f2ff1788ba25912c115b0aba5552a79484a1e50627b136c996498236111084c4131fb0fa47ba39d1ba8d9c6082d7136091846221210007d03ce1b40cd86402f016d0b2050c248118075828c12e09404801fc0b805602a815008e02400f007403801900b805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc8a6323129832bff5eeabf15e8ad65632af555aa8c53f29d54cea5251ca7c13d09c64da26a532e96f4ada53127091e481a2a910e87142ca0d103e8033ef1f20f627093809b90dae6ca35e9a68d0e67d3351960c865fe2fc177cba25c82dd166cb1857f2b81574a8e502272134897c4a224a11f88c245222110447be3c31c50da86762e21608ae0526281137892046c224108077c3841b90cb86182ec1500a104c824209904b825012005702b01540a801f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xc34609300d7a0bad5bcaa69518a7a536299d4c0a3c510284d4029e34e8a62d2f69654aaa53928c91d480a3c11ba8b9453215d05a80f3fc9f6cfa47bb3c91dfceda69b34599d8ccc66032c98d0c3860f2ff1788ba25912c115b0aba5552a794b0a2850627b136c99648d236115c88842f213104c7ee3e91ee8e746ea3671910c105ae289136098048c23a11888484021f40f386d03361900bc05b42c8143098849023009904b825012005702b01540a801f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x44f89310e1b42e844f91f0bdb7b0f59e9bcc78cf0ddebb6760e85ce397724e41c5b836f2dd1b53616aed0199b27644c59893055f6bc974aad554a95512a053aa594728a5049e9392614ba9612a25249c9191f2394628a510a0a3fc7d0f79e53c475ce81ca3886a4cd1922fa5acaa93c2604a49011922a424820fd1ec380698cd1862f45d0ab1502884e06a0d0198320410800fc1f01c0360680c8160280480800a0120200380400600800800 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd00668b2b98d0c4560d2cad628af95722b6558ea9954229e54cea4b521a7f13c69c44d9268d31c95f4a6a4f925290d482a32113687442e210506281c4009fc4fce6e73689ad0d42694340994cc806333101814bfe5c32d6964cb065772b294f8a5c52228813e89e84c524f92088de45d228910085c42220d0f3473837c19e0c705fa2b814609e44b424d11f08804262040fd071c3461920bb05b02c014509d84bc24c09904b825012005702b01540a801f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6c76b26a568f68267260d6065f55e85e45df5cd5c85c45b75af5a858757f56a55f55855253b53553152651a5124ee4d74c94ba4a849e48e47f47446b41540f3fd3f13eb3e63d23cd3c83bc3b23ab39038a37b37236c36435334b34833f3363303122fa2ec2e12d62ce2c22b62b12a92822622512342222101dc1c01b91a519c19117e17416e16414112c12511510e1060f50ee0e80e008508408208005105004f04e01f01e01d01c01901701401000a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame005_links_0000 record012_frame005_links_0064)
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x42c84907a07c097f8f09dcbb2752e9dd1b9871ee35c4b836fedbdb3b5f6aed51a8343676ce19a32c650c75893035f4bad72add59cb2161a7d4e49a12ea5b4ae9251f23c4708c91721e428824ff9fa3ec7a8f01db3ae744e69c036a6a4cf192318610bc1722de574a61442664ac9191621a4247e8f91e63ac738e11be344650c617a2e45a0ae154294518760ea1c83704b0941242401f03c0740e01902e0500800a0120200380400600800800 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame006_links_0000 record012_frame006_links_0064)
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd606a6b4fda46d156802e99722b6e5ac2d2d670b02576ab7558caa2545a8e944aa024f6277d3989964c0a5c52b493648fa3951ae8cb46122d915e8a644d224d11875039e1c6ce126fc3749ae4d4a6963419990c9c5fb2f39718b685a72ca1590aa0541297143c9f24be258129493849024492008ec47023510607a23a61aa8ca85dc29813c89ac49623c11688344001f20f206d432c1880b4056429412a08e843c20209904b825012005702b01540a801f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame007_links_0000 record012_frame007_links_0064)
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
def record012_frame008_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8138017f57db7cf7bc73972c7197086fe6f26d46c86c46b96a769f67b66e65e65264e64362561460a5fe5e95e15c55b95ad5a359859158757c57556f4d84c74b44a749e49047246645e45243b43340f3fe3ef3e33db3cf3ac39f39638837236a34d34033732d32231c3123073012fb2d82ab28e25323621b1ea1d11c61b21ac1a318f18717e17715413b13011c11410b0f90f30ea0e109909709409005705605505401f01e01d01c01901701401000a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record012) (record012.maps 8)
      (record012.inverseMaps 8) record012_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame008_links_0000 record012_frame008_links_0064)
theorem record012_frame008_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 8 :=
  of_group record012 8 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record012_frame008_indices record012_frame008_graph record012_frame008_links
def record012_frame009_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe507083789b0ad56687ada96a8b2f58b2c1d5e2ab654faa394eca5251d277d3949a74c9a60d2da93749024451f88d9461a1c109883040c9fecfd27d33db9e9cf2a63631017ecbc45d32de9608ad655a2a11478a0c4ab24b11cc8be44f21c900c7d83dd1e40e9471e33c18c0bf05ca2c715a8a7c50627313088f845221b0ff87c43b81ba0d6069832e1910c505ec2ea16e0b3854428613d09704a024211208604141fc09904b825012005702b01540a801f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record012_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 9)
      (record012.inverseMaps 9) record012_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame009_links_0000 record012_frame009_links_0064)
theorem record012_frame009_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 9 :=
  of_group record012 9 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame009_indices record012_frame009_graph record012_frame009_links
def record012_frame010_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7217107006e56da6c163663062061460c6005ec5e35dc5d25c85b958e58757656b56555954853f53652c5215124e54d64c94ba4a749a48a47b46f4643fc3f63e53d93d43c83b13a73a339a38e37f35434d33c33032c32130d3032fd2f42e72d82aa29a28f28026a25f25023e23422a20e1f81e91ce1bd1ad18717617016515f1571491421391321211151101071010f90ed0e80e10da09309209008c05505405305201f01e01d01c01901701401000a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 10)
      (record012.inverseMaps 10) record012_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame010_links_0000 record012_frame010_links_0064)
theorem record012_frame010_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 10 :=
  of_group record012 10 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record012_frame010_indices record012_frame010_graph record012_frame010_links
def record012_frame011_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86d85c85083782c81977776a75374573d7307137066fc6ef6d86c968c67e66265264a63b61b60d6025f35d75c658c57c56e56455554c54253452c5254924844684584504414214134083f93dd3cc38937c36535734f34232531830e3012ea2db2a929928b28127226925f2512492422252112051ea1dd1c81a719819018017917116115b15314c13512611e10e1070ff0ef0e90e10da09909709409005705605505401f01e01d01c01901701401000a009008007004003002001000 } : Fields).get c.val)
theorem record012_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record012) (record012.maps 11)
      (record012.inverseMaps 11) record012_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame011_links_0000 record012_frame011_links_0064)
theorem record012_frame011_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 11 :=
  of_group record012 11 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record012_frame011_indices record012_frame011_graph record012_frame011_links
def record012_frame012_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0651.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0651.count (({ width := 9, code := 0x14ca551e87419ecb6572893c9a4b219047e3d1b8cc421f0d8642e15058240e04fe7e3d5e8f378bbdd8eb74b9dc8d86bb55a8d36933598cb6531988bb5cad96ab459abd5cad562a54ea04fa79389a4ba59289247a31148741a04fa773b1d4e671371b4d66933190c66230178b65a2c158a644219047c2a148a04e160a85026120883c1808038180a04018080200 } : Fields).get c.val)
theorem record012_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record012) (record012.maps 12)
      (record012.inverseMaps 12) record012_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame012_links_0000 record012_frame012_links_0064)
theorem record012_frame012_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 12 :=
  of_group record012 12 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0651
    Papers.RationalityTen.SharedFrameCatalogue.group0651_facts record012_frame012_indices record012_frame012_graph record012_frame012_links
def record012_frame013_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0625.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0625.count (({ width := 9, code := 0x18fc6627077fbd5a6d165b1586bf5bad55ead53a8d2e9545a250a833c9d4e66d3398c9e49219047635178ac4a1f0280bf5f8f97c3cde0ef76ba9d0df6f36db2d86ab45a0ce66b258ec15eae972b65a2c15cac54295429d4c255208742208fe7e3d9e0ec73381b0d06631988c05c2d160a845221087e2b150a450180b8582a130903c1808038180a04018080200 } : Fields).get c.val)
theorem record012_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0625.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record012) (record012.maps 13) (record012.inverseMaps 13) record012_frame013_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record012) (record012.maps 13) (record012.inverseMaps 13) record012_frame013_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0625.localPairCheck (smallEmbedding record012) (record012.maps 13)
      (record012.inverseMaps 13) record012_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame013_links_0000 record012_frame013_links_0064)
theorem record012_frame013_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 13 :=
  of_group record012 13 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0625
    Papers.RationalityTen.SharedFrameCatalogue.group0625_facts record012_frame013_indices record012_frame013_graph record012_frame013_links
def record012_frame014_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0577.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0577.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record012_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0577.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0577.localPairCheck (smallEmbedding record012) (record012.maps 14) (record012.inverseMaps 14) record012_frame014_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0577.localPairCheck (smallEmbedding record012) (record012.maps 14) (record012.inverseMaps 14) record012_frame014_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0577.localPairCheck (smallEmbedding record012) (record012.maps 14)
      (record012.inverseMaps 14) record012_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame014_links_0000 record012_frame014_links_0064)
theorem record012_frame014_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 14 :=
  of_group record012 14 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0577
    Papers.RationalityTen.SharedFrameCatalogue.group0577_facts record012_frame014_indices record012_frame014_graph record012_frame014_links
def record012_frame015_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0483.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0483.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record012_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0483.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0483.localPairCheck (smallEmbedding record012) (record012.maps 15) (record012.inverseMaps 15) record012_frame015_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0483.localPairCheck (smallEmbedding record012) (record012.maps 15) (record012.inverseMaps 15) record012_frame015_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0483.localPairCheck (smallEmbedding record012) (record012.maps 15)
      (record012.inverseMaps 15) record012_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame015_links_0000 record012_frame015_links_0064)
theorem record012_frame015_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 15 :=
  of_group record012 15 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0483
    Papers.RationalityTen.SharedFrameCatalogue.group0483_facts record012_frame015_indices record012_frame015_graph record012_frame015_links
def record012_frame016_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0648.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0648.count (({ width := 8, code := 0xf5f3f1eeece8dedddbdad9d8d5d4d3d2cfcdc7c6c4c3c2c1bebdbcbbb8b6b1b0afaeadacabaaa9a8a1a09e9d9c9b9897969592908a898786858481807f7e7b7974737271706f6e6d6c6b6a686663615d595857565554535251504f4e4d4c4b4a49484746403f3d3a282726251615141312110f0c080706050403020100 } : Fields).get c.val)
theorem record012_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0648.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0648.localPairCheck (smallEmbedding record012) (record012.maps 16) (record012.inverseMaps 16) record012_frame016_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0648.localPairCheck (smallEmbedding record012) (record012.maps 16) (record012.inverseMaps 16) record012_frame016_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0648.localPairCheck (smallEmbedding record012) (record012.maps 16)
      (record012.inverseMaps 16) record012_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame016_links_0000 record012_frame016_links_0064)
theorem record012_frame016_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 16 :=
  of_group record012 16 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0648
    Papers.RationalityTen.SharedFrameCatalogue.group0648_facts record012_frame016_indices record012_frame016_graph record012_frame016_links
def record012_frame017_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0650.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0650.count (({ width := 9, code := 0xfb7cbdde8f27738dc4e06fb79bada6cb61aed46932d94c863b198ac260b017ebc5d2d166b258ac15eae56ab156a451a85409f4f26d34994c255268c45a2510874320d0481401f4f6753a1cce471381bcdc6d361acd26732188bc592c15cac552a14ca4512813c9c4d2612c94492411c8c401f8f47428138984a160a85026120883c1808038180a04018080200 } : Fields).get c.val)
theorem record012_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0650.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (smallEmbedding record012) (record012.maps 17) (record012.inverseMaps 17) record012_frame017_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (smallEmbedding record012) (record012.maps 17) (record012.inverseMaps 17) record012_frame017_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (smallEmbedding record012) (record012.maps 17)
      (record012.inverseMaps 17) record012_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame017_links_0000 record012_frame017_links_0064)
theorem record012_frame017_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 17 :=
  of_group record012 17 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0650
    Papers.RationalityTen.SharedFrameCatalogue.group0650_facts record012_frame017_indices record012_frame017_graph record012_frame017_links
def record012_frame018_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0647.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0647.count (({ width := 9, code := 0x110874321307823edf4f87bbd9eaf278bc1deec75391c6e17037dbcda6cb61aed368b2d94c963b1986c2602fd78b75b2d166b258ab558ab55299489e4ea6d34994c25528934923d1a874321506823f9f8f87b3c1d8e872379b4d4653218cc2602e970b4592b154a853289409a4c251248c3e1e8ec70271309448160a85026120883c1808038180a04018080200 } : Fields).get c.val)
theorem record012_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0647.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (smallEmbedding record012) (record012.maps 18) (record012.inverseMaps 18) record012_frame018_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (smallEmbedding record012) (record012.maps 18) (record012.inverseMaps 18) record012_frame018_indices (Fin.ofNat record012.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record012_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (smallEmbedding record012) (record012.maps 18)
      (record012.inverseMaps 18) record012_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record012_frame018_links_0000 record012_frame018_links_0064)
theorem record012_frame018_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 18 :=
  of_group record012 18 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0647
    Papers.RationalityTen.SharedFrameCatalogue.group0647_facts record012_frame018_indices record012_frame018_graph record012_frame018_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (Fin.cases (record012_frame008_supported hcells) (Fin.cases (record012_frame009_supported hcells) (Fin.cases (record012_frame010_supported hcells) (Fin.cases (record012_frame011_supported hcells) (Fin.cases (record012_frame012_supported hcells) (Fin.cases (record012_frame013_supported hcells) (Fin.cases (record012_frame014_supported hcells) (Fin.cases (record012_frame015_supported hcells) (Fin.cases (record012_frame016_supported hcells) (Fin.cases (record012_frame017_supported hcells) (Fin.cases (record012_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x322d8cec4d60e30097c2af45632ab54fca6751ca7c13d09c64da26a532e96f4ada53127091e481a1c506881f3ef1f20f627a63cf1e58f027753af1c20e026e236b9b20d7a69834399eccd465532197f0bf05d92e89708b745952c615e4ae05562a3941c9d24d2261928892848323091488844192088fc47be3d51e18e7471437d1b50d506762e21608ae0526281137892046c22410807ac3be1ce0e106e43501970c305d82c61500a104c824205702b01540a802f01680a804c01f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame001_links_0000 (interval_append _ 64 128 131 record013_frame001_links_0064 record013_frame001_links_0128))
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x30d9828c045ea2ec16f8a8c5362981440a014e8a62d2f69654aaa53928c91d480a3c11ba8b9453203cfb67d23c91dfceda75f3a81d14e527173781a60d16673333197ccb263130e1834bfc5e02e89628b045652ae954ca9e52528a14009ec4d526592488e045722410bc84c4181fb8fa47ba3ad1ce8e146ea36e1b38cf06443161820ba45ae289136098048c23a11888484021f40f3870c3681a50cd86403041780b685902a8143098849023005702b01540a802f01680a804c01f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame002_links_0000 (interval_append _ 64 128 131 record013_frame002_links_0064 record013_frame002_links_0128))
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x11422544486f0be11be17b0f4de33bd760e85ce397724e41c5b836f2dd1b53616aec9d8b3125f6bc974ae25beb716cad358cab1552a4544a7d4ea9451ca21412784e497d2ea564a89412724247c8d518a2544282cff9f43e0794f11da3a0728e21ae35267ccd197324624be9772d6584aa93c2604a49011922a424820fd1ec394700d81a6334640c317a2e8588ab1502884e0410800fc1f02904e0941181c0360680c8160280480800a0120200380400600800800 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame003_links_0000 (interval_append _ 64 128 131 record013_frame003_links_0064 record013_frame003_links_0128))
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
def record013_frame004_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x34119aacb26363125836b145722b1d508a67521a7f13c69c44d9268d31c95f4a6a4f925290d482a1d10828314009fc4fce7dc3e51edcefc76b39b9b90da26b13509a44d0265032018c0c406042ff96f0b5a58c2c195c0aca537297146ca204f827a132894848223991748a244421710888343e41e68ec07383901be0d4067833018e0c145fa2b814609e44b424d11f08804262040fd076038e1b40d186483001760b6058029e14509d84bc24c05702b01540a802f01680a804c01f00f007403801900b805002000a004802000e0040018008002000 } : Fields).get c.val)
theorem record013_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record013) (record013.maps 4)
      (record013.inverseMaps 4) record013_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame004_links_0000 (interval_append _ 64 128 131 record013_frame004_links_0064 record013_frame004_links_0128))
theorem record013_frame004_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 4 :=
  of_group record013 4 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record013_frame004_indices record013_frame004_graph record013_frame004_links
def record013_frame005_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6c86b56a76916856736065e85df5c85b75a858757f56a55f55855253b53553152651a5124c94a849e47f47446b46646045744e44a43b41440f3fb3f13e93e63d03cd3c63bc3b13ab38e38a37637236736434e34b34333f3343303162fe2ec2e42d62ce2c52b62b12a928a28226f26225b25123e23422f2222182101dc1c01b91a519c19117e17416e16414a14113512c12511c11510e1060fc0f50ee0e80e005105004f04e02f02d02a02601f01e01d01c01901701401000a009008007004003002001000 } : Fields).get c.val)
theorem record013_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record013) (record013.maps 5)
      (record013.inverseMaps 5) record013_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame005_links_0000 (interval_append _ 64 128 131 record013_frame005_links_0064 record013_frame005_links_0128))
theorem record013_frame005_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 5 :=
  of_group record013 5 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record013_frame005_indices record013_frame005_graph record013_frame005_links
def record013_frame006_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x10b612c1f821029febb9752e8dc7b896fedbdb3b5f6aed51a8343676ce19a32c650c0d75ae559cb2161abf570ac55329f5289e9392654ba9692ba4647c8ed1c23145c8650a2043fe7e0fb1e53c0764eb9cf39a70cdc1a9342648c61872f05c8b79642ba54ca61482884e89992f25649c9191621a4247e8f91e63ac738e11be358688cc1943185f8bd1722d0580ae1542945184b0941242402f05a0a81301f03c0740e01902e0500800a0120200380400600800800 } : Fields).get c.val)
theorem record013_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record013) (record013.maps 6)
      (record013.inverseMaps 6) record013_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame006_links_0000 (interval_append _ 64 128 131 record013_frame006_links_0064 record013_frame006_links_0128))
theorem record013_frame006_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 6 :=
  of_group record013 6 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record013_frame006_indices record013_frame006_graph record013_frame006_links
def record013_frame007_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0899.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0899.count (({ width := 8, code := 0xb0afaeadacaba3a19f9d9b999896959392908f8d8c8a8987868584838281807f7e7d7c7b7a797877767574737271706f6d6c6a696766646361605e5d5c5b5a59585756555453504e4c4a4947454342403f3d3b39383635343231302f2d2c2a29282625242321201f1e1d1c1b1a1918171615141312110f0d0b09080706050403020100 } : Fields).get c.val)
theorem record013_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0899.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record013) (record013.maps 7)
      (record013.inverseMaps 7) record013_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame007_links_0000 (interval_append _ 64 128 131 record013_frame007_links_0064 record013_frame007_links_0128))
theorem record013_frame007_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 7 :=
  of_group record013 7 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0899
    Papers.RationalityTen.SharedFrameCatalogue.group0899_facts record013_frame007_indices record013_frame007_graph record013_frame007_links
def record013_frame008_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1031.count (({ width := 10, code := 0x34cd2344ce735caaf6bbee9b82dab4ac6b02baad2b1ab6a3a769aa5a8fa2e6e97658922438fe3c8da2f8961e84e027f5f67c5ee7ade1771d9759d0735be6e9ae6a9a3685956458a621815fd765bd6457d5453d4c5053c4e5314a923471184510d419023f8fa3d8eb38ce1364d7350cd32cc8318bf2e8b52ccaf2a0a62889d2649724c8e2304a1244811c2e0b0290941f0781d0701905c140400a0240801c0400c0200400 } : Fields).get c.val)
theorem record013_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record013) (record013.maps 8)
      (record013.inverseMaps 8) record013_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame008_links_0000 (interval_append _ 64 128 131 record013_frame008_links_0064 record013_frame008_links_0128))
theorem record013_frame008_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 8 :=
  of_group record013 8 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1031
    Papers.RationalityTen.SharedFrameCatalogue.group1031_facts record013_frame008_indices record013_frame008_graph record013_frame008_links
def record013_frame009_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0921.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0921.count (({ width := 8, code := 0xb0afaeadacaba3a19f9d9b999896959392908f8d8c8a8987868584838281807f7e7d7c7b7a797877767574737271706f6d6c6a696766646361605e5d5c5b5a59585756555453504e4c4a4947454342403f3d3b39383635343231302f2d2c2a29282625242321201f1e1d1c1b1a1918171615141312110f0d0b09080706050403020100 } : Fields).get c.val)
theorem record013_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0921.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record013) (record013.maps 9)
      (record013.inverseMaps 9) record013_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame009_links_0000 (interval_append _ 64 128 131 record013_frame009_links_0064 record013_frame009_links_0128))
theorem record013_frame009_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 9 :=
  of_group record013 9 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0921
    Papers.RationalityTen.SharedFrameCatalogue.group0921_facts record013_frame009_indices record013_frame009_graph record013_frame009_links
def record013_frame010_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1019.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1019.count (({ width := 9, code := 0x476391a8bc56230681c01f8f97abcde2f0773b5d6e973b99c8e270375b6da6c35dacd56933994c660af172b75a2cd60ad552a54ca450a7938994ba51248e462250e83409f8fa793c1d0e672371b4d86b3499cca633097cba5b2c95caa522813c984b2491c8c4421908803f1f0f074391b8d46833188bc5c2713094481a0c85c2a1309044200f070301408038180a04018080200 } : Fields).get c.val)
theorem record013_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1019.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1019.localPairCheck (smallEmbedding record013) (record013.maps 10)
      (record013.inverseMaps 10) record013_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame010_links_0000 (interval_append _ 64 128 131 record013_frame010_links_0064 record013_frame010_links_0128))
theorem record013_frame010_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 10 :=
  of_group record013 10 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1019
    Papers.RationalityTen.SharedFrameCatalogue.group1019_facts record013_frame010_indices record013_frame010_graph record013_frame010_links
def record013_frame011_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x16d2d6da6b17606b3d0da0b3f270cd397525a4948b90f20a3ec6d8d11922f450893051ffbf87bef65e9bcf79af25debba760e31c43806f6dddb835c6acd31a133064abf97d2ef5d8b896eac6588af15aaa353ea0138a624b092120a3644886d09a063fe7e4f81ec3c6740e39c33726acd097e2de59cab14d28c4c894920230430839011f83e0788ec1ce3846d8d51a032c630510a013c2702f05a0a81301f03c0740e01902e0500800a0120200380400600800800 } : Fields).get c.val)
theorem record013_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record013) (record013.maps 11)
      (record013.inverseMaps 11) record013_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame011_links_0000 (interval_append _ 64 128 131 record013_frame011_links_0064 record013_frame011_links_0128))
theorem record013_frame011_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 11 :=
  of_group record013 11 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record013_frame011_indices record013_frame011_graph record013_frame011_links
def record013_frame012_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0xe21c1b7d6e6da9aeb3665ecb18eb1760ebc5782ec5ceb95712d95a6b45672c7586a5d442824e09a932a624c097d2c2554a08dd1aa2f4568a112a1c42c845062043fc794f19dc3b274ce89c53826e4dc1ae358660c71842fe5dcb916b2c8580ae1532a052ca214227a4d49612a24847c8b0fc1e83c4730e31bc34c680cc1923045d8b51662b8558a814e2904f09a1302504804b0941242402f05a0a81301f03c0740e01902e0500800a0120200380400600800800 } : Fields).get c.val)
theorem record013_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record013) (record013.maps 12)
      (record013.inverseMaps 12) record013_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame012_links_0000 (interval_append _ 64 128 131 record013_frame012_links_0064 record013_frame012_links_0128))
theorem record013_frame012_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 12 :=
  of_group record013 12 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record013_frame012_indices record013_frame012_graph record013_frame012_links
def record013_frame013_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0xff1fcbf57d0f7de7ba874ce85c9b886f6d75adb576a6d41a6b42678cdd9732463ebbd6f2d858eb055dab756cad559aaf552a6d4ca9752ca4d47a824fe9e9392684c892924a454868fd1ea2f456895102124207d4f51e03b2734e41bf3666b0d2196328644c718d3105f4ba9732ce570ab13a25a49c8f91922840c7f8f71de3886e0d81a4334638c517e2ec5a8af1562944f84b0941242402f05a0a81301f03c0740e01902e0500800a0120200380400600800800 } : Fields).get c.val)
theorem record013_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record013) (record013.maps 13)
      (record013.inverseMaps 13) record013_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame013_links_0000 (interval_append _ 64 128 131 record013_frame013_links_0064 record013_frame013_links_0128))
theorem record013_frame013_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 13 :=
  of_group record013 13 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record013_frame013_indices record013_frame013_graph record013_frame013_links
def record013_frame014_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x11fa3bc728c517625c1882101dfc3f27c8f29e23b976aec5d4b9c72ee49c6b7f6f6d59a0b38644c658931061ac25823005f6b756d2d1598b19602b155aa9d50a965249dd3aa6c4d499930a5049c9152023245e87508a043fc7d0f61e23ae730e21b835e6a0d099d326618c117e2f45c4b61562905089912e246458889092043e47a8ef1d038c700da1ac340648c71842f05b8530a41442802f05a0a81301f03c0740e01902e0500800a0120200380400600800800 } : Fields).get c.val)
theorem record013_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 14)
      (record013.inverseMaps 14) record013_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame014_links_0000 (interval_append _ 64 128 131 record013_frame014_links_0064 record013_frame014_links_0128))
theorem record013_frame014_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 14 :=
  of_group record013 14 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record013_frame014_indices record013_frame014_graph record013_frame014_links
def record013_frame015_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0579.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0579.count (({ width := 8, code := 0x8281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record013_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0579.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0579.localPairCheck (smallEmbedding record013) (record013.maps 15) (record013.inverseMaps 15) record013_frame015_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0579.localPairCheck (smallEmbedding record013) (record013.maps 15) (record013.inverseMaps 15) record013_frame015_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0579.localPairCheck (smallEmbedding record013) (record013.maps 15) (record013.inverseMaps 15) record013_frame015_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0579.localPairCheck (smallEmbedding record013) (record013.maps 15)
      (record013.inverseMaps 15) record013_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame015_links_0000 (interval_append _ 64 128 131 record013_frame015_links_0064 record013_frame015_links_0128))
theorem record013_frame015_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 15 :=
  of_group record013 15 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0579
    Papers.RationalityTen.SharedFrameCatalogue.group0579_facts record013_frame015_indices record013_frame015_graph record013_frame015_links
def record013_frame016_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0484.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0484.count (({ width := 8, code := 0x8281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record013_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0484.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0484.localPairCheck (smallEmbedding record013) (record013.maps 16) (record013.inverseMaps 16) record013_frame016_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0484.localPairCheck (smallEmbedding record013) (record013.maps 16) (record013.inverseMaps 16) record013_frame016_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0484.localPairCheck (smallEmbedding record013) (record013.maps 16) (record013.inverseMaps 16) record013_frame016_indices (Fin.ofNat record013.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record013_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0484.localPairCheck (smallEmbedding record013) (record013.maps 16)
      (record013.inverseMaps 16) record013_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record013_frame016_links_0000 (interval_append _ 64 128 131 record013_frame016_links_0064 record013_frame016_links_0128))
theorem record013_frame016_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 16 :=
  of_group record013 16 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0484
    Papers.RationalityTen.SharedFrameCatalogue.group0484_facts record013_frame016_indices record013_frame016_graph record013_frame016_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (Fin.cases (record013_frame004_supported hcells) (Fin.cases (record013_frame005_supported hcells) (Fin.cases (record013_frame006_supported hcells) (Fin.cases (record013_frame007_supported hcells) (Fin.cases (record013_frame008_supported hcells) (Fin.cases (record013_frame009_supported hcells) (Fin.cases (record013_frame010_supported hcells) (Fin.cases (record013_frame011_supported hcells) (Fin.cases (record013_frame012_supported hcells) (Fin.cases (record013_frame013_supported hcells) (Fin.cases (record013_frame014_supported hcells) (Fin.cases (record013_frame015_supported hcells) (Fin.cases (record013_frame016_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xb925c52e116e4b6a5a92bed5e8ad45632aed55aa8a53f29cd4cea4f51ca7bd3d09c44da269d32e96d4ada52927091b481a1c506881f3ef1f20f627a63cf1e58f027753af1c20e026e236b9b20d7a69834399eccd465532197f4bf05dd2e89718b745992c615f4ae055a2a39348944494230914888443121110608224011f70f7c7a43c31d68e647143791b50d406762f31710b485822b81538a4c50226f12d092046c22410807b43be1d00e106e43541970c305d82ca1500a104c824205702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame001_links_0000 (interval_append _ 64 128 141 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4559dacd162eb065732a5d518a7753629994c0a3951028454029e14e8a6252f69634aaa53528c91a480a3b91ba8b7453203cfb67d23c91dfceda75f3a81d14e527173781a60d16673333197ccb263130e1834bfc5e02e89638b045692ae9550a9e52928a14109ec4d9265915c85e4261fb8fa47ba3c91db8ea473a38f1c08dd46da3671a80ce06443131820b985ae29c14489dc4d8260128891847423111188484021f40f387143681a70cd86403081780b685902ac143098849023005702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame002_links_0000 (interval_append _ 64 128 141 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x414821032054077faf8df0bda7b0f55e9bca78cf05debb4760e81ce396724e3dc5b816f2dc9b535f6aec9d8b3125f6bc974ae25beb716cad358cab1552a4544a7d4ea9451ca21412784e49812ea574a89452724447c8dd18a274427d0f29e23a0728e21bb3686b4d49a533c668cb192320618be9742d6578aa9402784d0981292484808c91521c424820fd1ec398700d91a6334648c317a2e8598ab1502884e0410800fc1f01c0360680c81702c0540a0130240440800a0120200380400600800800 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame003_links_0000 (interval_append _ 64 128 141 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xbfa5f5af7976aba85c22ca1628af65722b5958ea9654229d94cea4a521a7e53c69c14d9268131c95c4a6a4ed25290c482a1d10828314009fc4fce7dc3e51edcefc76b39b9b90da26b13509a44d0265032018c0c406042ff9700b5a5902c195d0aca53b297147ca204f927a12088ba451217108883440b1fb0f8079a3be1d60e7071837c1af0d3067832c18e0c105fa2cd15c0a88518279133896849a23e11688804262040fd076838e1b60d186483041760b605802a214509d84bc24c05702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame004_links_0000 (interval_append _ 64 128 141 record014_frame004_links_0064 record014_frame004_links_0128))
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x65f65564e64563e63260c6065f25e85e25df5cb5c85c15b75ae5a858657f56855f55655253953552f5265195124c94a849e47f47446b46646045744e44a43b41440f3fb3f13e93e63d03cd3c63bc3b13ab38f38a37937236a36435134b34633f3353302ec2d62ce2b62b12a929f29228928227826b26225825124623b23422b2222172101ec1dc1d01c01b91af1a519c19118817e17416e16414b14113612c12511e11510e1060fe0f50ee0e80e005105004f04e01f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame005_links_0000 (interval_append _ 64 128 141 record014_frame005_links_0064 record014_frame005_links_0128))
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
def record014_frame006_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x3f07dafa9f0bde7aaefddcbaf752e99d1b9571ee31c4b826fedb5b3b5d6aed4da8341676cdd9a32b650c0d75ae559cb2161abf570ac55329f5289e9392654ba9692ba4647c8ed1c23145c8710a2073fe7e4fb1e83c0768eb9d039a6a4c918c2f05c8b796d2d0584ae9572a0530a394427c4dc9992e2564989191922c448869092043f47c8f31e03ac738e11be360688cd194318600bd1722d0588ae1542945184b0941242401f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record014_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record014) (record014.maps 6)
      (record014.inverseMaps 6) record014_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame006_links_0000 (interval_append _ 64 128 141 record014_frame006_links_0064 record014_frame006_links_0128))
theorem record014_frame006_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 6 :=
  of_group record014 6 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record014_frame006_indices record014_frame006_graph record014_frame006_links
def record014_frame007_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0899.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0899.count (({ width := 8, code := 0xaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999796949391908e8d8b8a8887868584838281807f7e7d7c7b7a797877767574737271706f6e6c6b696866656362605f5d5a585755545352514f4e4d4b4a484746444341403e3d3c3b3a393837363534333231302f2e2c2b29282725242322201f1e1d1c1b1a1914131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0899.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record014) (record014.maps 7)
      (record014.inverseMaps 7) record014_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame007_links_0000 (interval_append _ 64 128 141 record014_frame007_links_0064 record014_frame007_links_0128))
theorem record014_frame007_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 7 :=
  of_group record014 7 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0899
    Papers.RationalityTen.SharedFrameCatalogue.group0899_facts record014_frame007_indices record014_frame007_graph record014_frame007_links
def record014_frame008_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1031.count (({ width := 10, code := 0x31fc7319c470ec1af9bdaf2bbeecba6e3b82ddb6ad5b4ac5b02b9ad2b0ab6a2a7699a5a8ea2e6e97658922438fe3c8da2f8961e84e027f5f67c5ee7ade1771d9759d0735c16e9b16a9a4685986458b621825fd645514f5053c4e5374d12e4a9264811c45d144410a419013f8f93d8ee3ace738ce1374d935cd4344cd32cc8318c12e8b62ccaf2a4a62889d2689724c8e2304a1244811c1f0781d0701a0641805c15050110400a0240801c0400c0200400 } : Fields).get c.val)
theorem record014_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record014) (record014.maps 8)
      (record014.inverseMaps 8) record014_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame008_links_0000 (interval_append _ 64 128 141 record014_frame008_links_0064 record014_frame008_links_0128))
theorem record014_frame008_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 8 :=
  of_group record014 8 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1031
    Papers.RationalityTen.SharedFrameCatalogue.group1031_facts record014_frame008_indices record014_frame008_graph record014_frame008_links
def record014_frame009_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0921.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0921.count (({ width := 8, code := 0xaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999796949391908e8d8b8a8887868584838281807f7e7d7c7b7a797877767574737271706f6e6c6b696866656362605f5d5a585755545352514f4e4d4b4a484746444341403e3d3c3b3a393837363534333231302f2e2c2b29282725242322201f1e1d1c1b1a1914131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0921.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record014) (record014.maps 9)
      (record014.inverseMaps 9) record014_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame009_links_0000 (interval_append _ 64 128 141 record014_frame009_links_0064 record014_frame009_links_0128))
theorem record014_frame009_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 9 :=
  of_group record014 9 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0921
    Papers.RationalityTen.SharedFrameCatalogue.group0921_facts record014_frame009_indices record014_frame009_graph record014_frame009_links
def record014_frame010_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0909.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0909.count (({ width := 9, code := 0x1a5d0e7f3b9bcd65f2990c76331588c36130581bf5eef376ba5cee370b75b6d76ab457ab156a8d3e9d4ca350a7d3a9c4ca5f2a93c96451f8e46a2f1689c3a19088341204ff7ebedf2f77abadcae36f371b6d76a34d9eca6330d7ebc5cad564ae55aa94ca14ea692c9548a35168943209007e3e9e4ec72379b4d26631984bc5b2c158aa351a0cc641b0d06430160a85026110803c1c0a048200e04018080200 } : Fields).get c.val)
theorem record014_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record014) (record014.maps 10)
      (record014.inverseMaps 10) record014_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame010_links_0000 (interval_append _ 64 128 141 record014_frame010_links_0064 record014_frame010_links_0128))
theorem record014_frame010_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 10 :=
  of_group record014 10 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0909
    Papers.RationalityTen.SharedFrameCatalogue.group0909_facts record014_frame010_indices record014_frame010_graph record014_frame010_links
def record014_frame011_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79ea9e59d498a98397696c96095593492b91f9128f48e78a689a88887d86e85f83982c81e80b7e27d17507137006c86b56a269869469068067c66a62761f6126095fe5f25d15c85be5b058f58254c54453652c5215144f14e64dc4ce4ae4a04364043f53c73b83a839c39538837d37936b35e35034332d31e3113032f32d72cb29528527426625a24823822821a2081f91e91db1cd1b91ad19f19018317216415614613612a11c10b0fe05505405305201f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record014_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 11)
      (record014.inverseMaps 11) record014_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame011_links_0000 (interval_append _ 64 128 141 record014_frame011_links_0064 record014_frame011_links_0128))
theorem record014_frame011_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 11 :=
  of_group record014 11 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record014_frame011_indices record014_frame011_graph record014_frame011_links
def record014_frame012_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x4c297f2f65dcb99692624bc8e9132163f46e8d519a2f4548970e21bc2d8510960fc0b809001fb3e77b8e7dc63856d6d89aeb586aad4da8b4e68ec9992b1d630c55883035fcbe97a2ea5c4b35662c457cae95a2a553ca6d4aa874fa9311fa3a44c87d0da1642683d062083f87dcf91e83c2754e79ca3806d4d7997322634c29802f25bcb395e2a4524a013726649c9011c22c440849011f43c4728da1a23105d04909011c2301f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record014_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record014) (record014.maps 12)
      (record014.inverseMaps 12) record014_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame012_links_0000 (interval_append _ 64 128 141 record014_frame012_links_0064 record014_frame012_links_0128))
theorem record014_frame012_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 12 :=
  of_group record014 12 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record014_frame012_indices record014_frame012_graph record014_frame012_links
def record014_frame013_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x4f09df3ba744e69bd326634c19792e65b4a89452724bc8e9111be364688c717e2e4488790ce14c1a826f21d53a270edf9b9b6b6d4da5b235f6acd019db35662cb194b21638c5587b045feb9570ade5b6b5d6aac9580ae15729f5349611f235438851062034007e8fb9f53e27b0f49e63be758e61c33786b0d29882fa5dcb79692c2574aa14e28c4fc9d13325a4788990a2083fc7c0f31d63946e8d41963045c04909011c2301f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record014_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record014) (record014.maps 13)
      (record014.inverseMaps 13) record014_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame013_links_0000 (interval_append _ 64 128 141 record014_frame013_links_0064 record014_frame013_links_0128))
theorem record014_frame013_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 13 :=
  of_group record014 13 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record014_frame013_indices record014_frame013_graph record014_frame013_links
def record014_frame014_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0509.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0509.count (({ width := 8, code := 0xf7f6f5f4f3f0ebeae9e8e7e6e5e4e3e2dfded9d8d7d6d5d4d3d2d1d0cecdc6c3c2c1bfbdbbbab9b8b7b4afaeadacabaaa9a8a7a6a3a29d9c9b9a99989796959492918a87868583817f7e7d7c7b7a797877767472706e6b696563615f5e5c5a595857565553514e4c4a4847454342413f3d3c3b3a2a2928271c1b1a1917161514131211100a0908070403020100 } : Fields).get c.val)
theorem record014_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0509.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record014) (record014.maps 14)
      (record014.inverseMaps 14) record014_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame014_links_0000 (interval_append _ 64 128 141 record014_frame014_links_0064 record014_frame014_links_0128))
theorem record014_frame014_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 14 :=
  of_group record014 14 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0509
    Papers.RationalityTen.SharedFrameCatalogue.group0509_facts record014_frame014_indices record014_frame014_graph record014_frame014_links
def record014_frame015_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0576.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0576.count (({ width := 8, code := 0x8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0576.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0576.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0576.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0576.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0576.localPairCheck (smallEmbedding record014) (record014.maps 15)
      (record014.inverseMaps 15) record014_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame015_links_0000 (interval_append _ 64 128 141 record014_frame015_links_0064 record014_frame015_links_0128))
theorem record014_frame015_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 15 :=
  of_group record014 15 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0576
    Papers.RationalityTen.SharedFrameCatalogue.group0576_facts record014_frame015_indices record014_frame015_graph record014_frame015_links
def record014_frame016_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xce166732fd91cc7861eae8d722b6b5ac2d21670aff576ab6958ca9f545a8dd44a9ff4f627713989934c0a5b92b493348fa32d16c8af44d224d118881436216104680e3ed9d34e787183849be4dd26b63529a4cd0666132717e0bce5c32da1690b285612a814f8a5c50c27c929492048923b11c08d445b22210b08304031f40f447743a61bf8da06aa33f1950c085dc2a814c0a244f226b12d092c47822d10e08344001f20f2071436a1a60cb06202ee1680ac852827212a08e843c20205702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record014_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 16) (record014.inverseMaps 16) record014_frame016_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 16) (record014.inverseMaps 16) record014_frame016_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 16) (record014.inverseMaps 16) record014_frame016_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 16)
      (record014.inverseMaps 16) record014_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame016_links_0000 (interval_append _ 64 128 141 record014_frame016_links_0064 record014_frame016_links_0128))
theorem record014_frame016_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 16 :=
  of_group record014 16 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record014_frame016_indices record014_frame016_graph record014_frame016_links
def record014_frame017_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcb8651b2458b2c466052d9d6a8b2c58b2c115e2ab354faa2d4eca4f51d27713949a44c9a6012da93449024391f88d6461a0c0ff67e93db9e9cf2a7843b79d74e4a71236b18ccc405f82f11740b7a57f2b5955ca8451b28312a092c47022f91308724001f60f687903a21c78bf058e2b514189cc4c2255127091447c23911808a444421b10788183fe1f80f8878c3b81c10dd06cc3581a60cf065c32218a0c105ec2ea16e0b385602a214a0a184f426a12e094048423211208604141fc05702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record014_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 17) (record014.inverseMaps 17) record014_frame017_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 17) (record014.inverseMaps 17) record014_frame017_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 17) (record014.inverseMaps 17) record014_frame017_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 17)
      (record014.inverseMaps 17) record014_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame017_links_0000 (interval_append _ 64 128 141 record014_frame017_links_0064 record014_frame017_links_0128))
theorem record014_frame017_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 17 :=
  of_group record014 17 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame017_indices record014_frame017_graph record014_frame017_links
def record014_frame018_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x69769368b68167b66b63563061e61460a6005ea5e35da5d25c55b958d58757456b56255954653f53352c51e5124c94a749a47b46f46445d4574544464424313fb3f63e33d93d23c83af3a73a139a38b37f35334d33933032a32130a3032fb2f42e42d828f26a25f23e23422a22121921220e2091ff1f81f01e91e11d71ce1c61bd1b41ad18f18717e17617016b16515f15714e14914213913212712111b11511010c1071010f90f20ed0e80e10da05505405305201f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record014_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 18) (record014.inverseMaps 18) record014_frame018_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 18) (record014.inverseMaps 18) record014_frame018_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 18) (record014.inverseMaps 18) record014_frame018_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 18)
      (record014.inverseMaps 18) record014_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame018_links_0000 (interval_append _ 64 128 141 record014_frame018_links_0064 record014_frame018_links_0128))
theorem record014_frame018_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 18 :=
  of_group record014 18 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record014_frame018_indices record014_frame018_graph record014_frame018_links
def record014_frame019_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x67166b66565764f6386035fc5f05e75e25dd5cd5c35ba5b159c59156655e54f54653f5395225155094fe4e74da49247546e45144843d43542f42941b4123fe3c73be3b43ad3a63a139138737d37235c35332a32131230a3032fd2e62d92cb2be2a629b24f2392322152092001f91f11ea1e31dd1d61cf1cb1c81c11b91b21ac1a419418c17817116a16415d15414e14714013d13913513012911d11911310c1070ff0f80f30ed0ea0e50e00db0d505605505405301f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record014_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 19) (record014.inverseMaps 19) record014_frame019_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 19) (record014.inverseMaps 19) record014_frame019_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 19) (record014.inverseMaps 19) record014_frame019_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record014) (record014.maps 19)
      (record014.inverseMaps 19) record014_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame019_links_0000 (interval_append _ 64 128 141 record014_frame019_links_0064 record014_frame019_links_0128))
theorem record014_frame019_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 19 :=
  of_group record014 19 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record014_frame019_indices record014_frame019_graph record014_frame019_links
def record014_frame020_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0938.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0938.count (({ width := 9, code := 0x184c1e0b037fbddcee570b7dbadb6ab459ac960af55ead53a95429f48a2d067d389ac9643208dc662f158a44e2510864120701803fdfcfb7cbddeaf177ba1cee471b85c0d96b3499ec9632d964b1562a950a65228942a04f275389b4d25d289247a311282401f8f87b3c9dcec75399c4de6d35994c6612f978b85a2c960ac532893c9a32188c05e1c0d86832170b054281309044200a048200e04018080200 } : Fields).get c.val)
theorem record014_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record014) (record014.maps 20) (record014.inverseMaps 20) record014_frame020_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record014) (record014.maps 20) (record014.inverseMaps 20) record014_frame020_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record014) (record014.maps 20) (record014.inverseMaps 20) record014_frame020_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record014) (record014.maps 20)
      (record014.inverseMaps 20) record014_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame020_links_0000 (interval_append _ 64 128 141 record014_frame020_links_0064 record014_frame020_links_0128))
theorem record014_frame020_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 20 :=
  of_group record014 20 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0938
    Papers.RationalityTen.SharedFrameCatalogue.group0938_facts record014_frame020_indices record014_frame020_graph record014_frame020_links
def record014_frame021_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6cd6c26bb6a169b68565164763462b62261c5fb5f25e95e25ce5c85a459858457c57456e54f54753e53752251c4d34ba4b249448a48147d47146b45344c4354013f73e23d93d03c93a839f39639037e3783543483313293203192fa2f22ea2e42d22cc28326425a24123923122b22421b21520f2041fb1f41ec1de1d31ca1c31bb1af1ab19719018918217d17416c16415b15114914113813112812211d11811310b1050ff0f90f10eb0e50df0d905705605505401f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record014_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 21) (record014.inverseMaps 21) record014_frame021_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 21) (record014.inverseMaps 21) record014_frame021_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 21) (record014.inverseMaps 21) record014_frame021_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 21)
      (record014.inverseMaps 21) record014_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame021_links_0000 (interval_append _ 64 128 141 record014_frame021_links_0064 record014_frame021_links_0128))
theorem record014_frame021_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 21 :=
  of_group record014 21 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record014_frame021_indices record014_frame021_graph record014_frame021_links
def record014_frame022_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1025.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1025.count (({ width := 9, code := 0x173b85bad166b0d62ab50a6d329744a0d027f3c9dcda673096cb2572591486411c8dc4e19098240600fe7dbe5e6f17638dc0db6c35daccf6632d94c7633057cbb5c2dd6cb056ab156a7532792e9447a31168a4421104813e9ecf4793b9cce270379b4d8673298cc25f2d964ae54291409c4b2511c8a43211047c3d1e0e870371b0d0662311084401b0d06430160a8502611080381a090401c0c04018080200 } : Fields).get c.val)
theorem record014_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1025.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record014) (record014.maps 22) (record014.inverseMaps 22) record014_frame022_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record014) (record014.maps 22) (record014.inverseMaps 22) record014_frame022_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record014) (record014.maps 22) (record014.inverseMaps 22) record014_frame022_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record014) (record014.maps 22)
      (record014.inverseMaps 22) record014_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame022_links_0000 (interval_append _ 64 128 141 record014_frame022_links_0064 record014_frame022_links_0128))
theorem record014_frame022_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 22 :=
  of_group record014 22 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1025
    Papers.RationalityTen.SharedFrameCatalogue.group1025_facts record014_frame022_indices record014_frame022_graph record014_frame022_links
def record014_frame023_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0898.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0898.count (({ width := 8, code := 0x8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0898.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0898.localPairCheck (smallEmbedding record014) (record014.maps 23) (record014.inverseMaps 23) record014_frame023_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0898.localPairCheck (smallEmbedding record014) (record014.maps 23) (record014.inverseMaps 23) record014_frame023_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0898.localPairCheck (smallEmbedding record014) (record014.maps 23) (record014.inverseMaps 23) record014_frame023_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0898.localPairCheck (smallEmbedding record014) (record014.maps 23)
      (record014.inverseMaps 23) record014_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame023_links_0000 (interval_append _ 64 128 141 record014_frame023_links_0064 record014_frame023_links_0128))
theorem record014_frame023_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 23 :=
  of_group record014 23 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0898
    Papers.RationalityTen.SharedFrameCatalogue.group0898_facts record014_frame023_indices record014_frame023_graph record014_frame023_links
def record014_frame024_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1030.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1030.count (({ width := 9, code := 0x1b1d76b34ba3cee57258fc662b1183c05faf978bb5bed767b1d86bf59aad4ea34da5d0677389a4c6612e95ca645208d44a1f0c84c1e0b007ebedf2f579bb1d0e470379b8d6693419cca642f970b558ab95aac5529946a24f26d34994ba4d208f47231168843a1104813f1f0f6793b9d4e872389b8d86933998c66130178b85a2c95cac34198c8621f0f074381a0c8602e150a044200a048200e04018080200 } : Fields).get c.val)
theorem record014_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1030.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record014) (record014.maps 24) (record014.inverseMaps 24) record014_frame024_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record014) (record014.maps 24) (record014.inverseMaps 24) record014_frame024_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record014) (record014.maps 24) (record014.inverseMaps 24) record014_frame024_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record014) (record014.maps 24)
      (record014.inverseMaps 24) record014_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame024_links_0000 (interval_append _ 64 128 141 record014_frame024_links_0064 record014_frame024_links_0128))
theorem record014_frame024_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 24 :=
  of_group record014 24 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1030
    Papers.RationalityTen.SharedFrameCatalogue.group1030_facts record014_frame024_indices record014_frame024_graph record014_frame024_links
def record014_frame025_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0920.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0920.count (({ width := 8, code := 0x8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0920.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record014) (record014.maps 25) (record014.inverseMaps 25) record014_frame025_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record014) (record014.maps 25) (record014.inverseMaps 25) record014_frame025_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record014) (record014.maps 25) (record014.inverseMaps 25) record014_frame025_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record014) (record014.maps 25)
      (record014.inverseMaps 25) record014_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame025_links_0000 (interval_append _ 64 128 141 record014_frame025_links_0064 record014_frame025_links_0128))
theorem record014_frame025_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 25 :=
  of_group record014 25 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0920
    Papers.RationalityTen.SharedFrameCatalogue.group0920_facts record014_frame025_indices record014_frame025_graph record014_frame025_links
def record014_frame026_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0908.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0908.count (({ width := 9, code := 0x1218fc7a3b1c8dc662f158a44e25118843e1d0d85c260f058240e0501803fdfcfd7dbd1deed74b9dcce471385c0df6f371b4d86bb59aad469b49a2d06733194c863b198ac461b0982c05f2dd64b0562a952a65228d429e4e26930964a249208e4622d1285411fcf87b3b9d0e470369a8d06632984bc5b2c15ca6502713092462210882291409c4c1b0d06430160a85026110803c1c0a048200e04018080200 } : Fields).get c.val)
theorem record014_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0908.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record014) (record014.maps 26) (record014.inverseMaps 26) record014_frame026_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record014) (record014.maps 26) (record014.inverseMaps 26) record014_frame026_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record014) (record014.maps 26) (record014.inverseMaps 26) record014_frame026_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record014) (record014.maps 26)
      (record014.inverseMaps 26) record014_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame026_links_0000 (interval_append _ 64 128 141 record014_frame026_links_0064 record014_frame026_links_0128))
theorem record014_frame026_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 26 :=
  of_group record014 26 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0908
    Papers.RationalityTen.SharedFrameCatalogue.group0908_facts record014_frame026_indices record014_frame026_graph record014_frame026_links
def record014_frame027_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x62d62a62661c61860e5da5d55cb5c15bb5b159b59058a57d56e5605395315245185115064ee4e44e04d44c14b346543c4304104073fb3f43f13ed3e33df3d53a239d39038c38237c36035b34f34933232a2ff2fa2ea2e32d72cf2b32ae2a429e28727c22c2031f71d71ce1c21bb1b91b51b01ac1a61a019a19418b18517f17a17516a16415314e14814213d13713112d12912411e1181131101091040ff0fa0f60ef0e90e50e00d90d30cf0c90c505004f04e04d01f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record014_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 27) (record014.inverseMaps 27) record014_frame027_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 27) (record014.inverseMaps 27) record014_frame027_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 27) (record014.inverseMaps 27) record014_frame027_indices (Fin.ofNat record014.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record014_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 27)
      (record014.inverseMaps 27) record014_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record014_frame027_links_0000 (interval_append _ 64 128 141 record014_frame027_links_0064 record014_frame027_links_0128))
theorem record014_frame027_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 27 :=
  of_group record014 27 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record014_frame027_indices record014_frame027_graph record014_frame027_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (Fin.cases (record014_frame006_supported hcells) (Fin.cases (record014_frame007_supported hcells) (Fin.cases (record014_frame008_supported hcells) (Fin.cases (record014_frame009_supported hcells) (Fin.cases (record014_frame010_supported hcells) (Fin.cases (record014_frame011_supported hcells) (Fin.cases (record014_frame012_supported hcells) (Fin.cases (record014_frame013_supported hcells) (Fin.cases (record014_frame014_supported hcells) (Fin.cases (record014_frame015_supported hcells) (Fin.cases (record014_frame016_supported hcells) (Fin.cases (record014_frame017_supported hcells) (Fin.cases (record014_frame018_supported hcells) (Fin.cases (record014_frame019_supported hcells) (Fin.cases (record014_frame020_supported hcells) (Fin.cases (record014_frame021_supported hcells) (Fin.cases (record014_frame022_supported hcells) (Fin.cases (record014_frame023_supported hcells) (Fin.cases (record014_frame024_supported hcells) (Fin.cases (record014_frame025_supported hcells) (Fin.cases (record014_frame026_supported hcells) (Fin.cases (record014_frame027_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6806716246195d25c75a959f59054251c5084c549b47747146c46545a45242241a3c83c039738933d33731a31130b2ff2d62d02ba2b42a429a29729427726825324423e23621620b2011fb1f31eb1be1b31ad19418e1861781661621431010f10e60dc0cb0c00ba0a006906205f05905305204604403d03903503302c02902301d01c01901701400f00e00a008007005003002001000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x10d603c037f2fc5e53a974ee35bc34d694ce993b13620c117caf15cab6d6aad0570ac9492774de8f91aa2b4488690c2123e87ace69c93846f8d89aa340674ca98f2fc5dcb69682844e4949222083f47a0ee1c83806c0d11943145e0b014a2804d0810fa1b43605e0b415c298500941241c8360620b0148230400740e00f01c0280400700600800800 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xc046002ec16f8a5f50fa62d2f69654aaa53928c91247822e509081d3f49f48f2277f3b69d7cea074532f9960c3660d2f01628b045652ae954ca9e50026a920c8e046122410e484c4181fb0fa47ba3ad1ce8e146ea36e1b38cdc6463161748a2046221310007d03ce1c30da06943361900c105e02da1640aa04902300fa075828c0e607002e01580aa05402400ec07002f01680a804c02400f007403801900b805001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x19e4ce1669b1817fcbc95ccad9569eafa5792b695a4aca562aa5d51ea77537a9994c2a2950427c53b09c14daa53528e90746aa27910a84e40d1f98fa47b03ca1df4ed670a37f9b8cdb06cd3641a60d1c673334997ccb462430217bcbae5c22db1550aa051a277130c96448922f10d884c40e1fc8f9c7b63a91c08db467231417b8b9c5942bf14e09dc4c025111d08c43fe1f20f2869c30816409803a81900a004e825812605b02d01580aa023011007803a01a00c005401e00e00680280120080018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c8ee3771535b19a6cac64db2198f4bfe5faaf5178abb05d0ad716a6b32591ac395feacf560aae5558aa454ea7b53b498d4afa4a12148da45621d50ae84641f20d905e7ae3d11dfcede75a3a49c10df06d53629ac0d3e6703311968c9a64531f96ccb4256629f14489f84d925892148de46222e11588a24151e98e9c6bc33e18f8c345dc2dd15e8a744fc26c12688f044621c10a872c31a15709803cc1a40a004e825812605b02d01580aa023011007803a01a00c005401e00e00680280120080018008002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2026fde7daba85b92d7d69db3d199ac35610afd57c2bca5dbad9d6aeb2c58cac115e8aa753fa989484a27509a6012e092647a22ed13486b41e201cfd27cd3dc9e94f267013769b04d5a69634198ccc465f82f29740b805732a594b8a1c4f326f91308783f21e00e1c6cc3371840b4c56a29914289c44be245118088840e1f90f607903ae1d00e086cc34c19e0c886282e616c0b2852826a12108583a01aa0a004e825812605b02d01580aa023011007803a01a00c005401e00e00680280120080018008002000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6cc6c669669067b6746636256205e85e35cc5c45b159657d56754551e5094e24c64a949449042a3d03b93b038437e36e36335834d32631d3002fd2de2cd2b12a729a29729427b27526325624d24021b20e1ec1e81c51b619518a17a17517115614413712711610b0e70c409e08606706506306005a05805405305204504103b03803403102402201e01d01c00f00d009008007004003002001000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x37ddbd6d2868c3345950c615c92e19586ab3536290d3f89ba4d2a65d2f89594a624a12268ff474a38d00e7203679aa8c1a5f92eb9708b6259b2a614b49e24e124e11d08804231ff8fc07c239e1c50da06a63421960b7457c28213908b440a1d10da06403021720a684fc26612a08f045c1fa0e305882300d206703281880b805a02b01540a804702100ec070034018809004401e00e807001e00d004802000e0040018008002000 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6c669067b6746636256205e85e35cc5c45b159757f5695094a949449048547c47443842a3de3d03b93b038337e36c36335634d32631d3002fd2de2cd2b12a729a29729427927525e25624824022421b20e1fd1ec1e81c51bf1b61a619518a17a17517115814613712a11610b0e70c409e08606705a05805405305204504103b03803403102402201e01d01c01a01801500f00d009008007004003002001000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x73e7136da6d36ce69468e6816756145c75c359858950d5084ed4dd48c48847647144442640d4063fb3d93923883583482d92cb2ad29b2582472422332181e11d41cd1c21b81b31a91a319d19717115114c14a14413512f12d11211010b1060fd0f80ed0e70e00ce0c50bd0b70b40b108608506e06a06405e05b05405204e04d03c03803302c02902302001d01c00f00e00a008007003002001000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x83e7f87ba7b77ac78678077b7757316c86c369367f5fd5f85db5c857356f56556154b53852952251c4df47246342d41739638736234c3012f72f32e92dd2bd2b62b02ab29028827526625e24f2041c01ba1b71af19c19418f15f15814513d13212c11c1141070e60d80cc0c80c40c109209107607106b06506205b05905505403d03803302c02902302001d01c00f00e00a008007003002001000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0249.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0249.count (({ width := 9, code := 0x4b243168ac521f0e86c3208f67a3bddadf6f36db0cc65b2992c660afd7cbd5e2c15aa652a692e93482110682409fcf0773b1d4e873389c0de6e34984c05f2f170b65a29948a04f27134964a2410c82401f8f87a33190b056281309444200f878361a0b8542811078381a09040180a04018080200 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0249
    Papers.RationalityTen.SharedFrameCatalogue.group0249_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
def record021_frame004_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0146.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0146.count (({ width := 8, code := 0xc2bcb6b5b4b2b1b0afaca5a4a09f999895938d8c8b8a8784838281807a7874736e6c696761605f5e5c5857565554535251504f4d494847464443423e3d3b3a3938363534312f2e2d2c2b252421201f1d1c1b19181715141311100f0d0c0b090806050403020100 } : Fields).get c.val)
theorem record021_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0146.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0146.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0146.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record021_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0146.localPairCheck (smallEmbedding record021) (record021.maps 4)
      (record021.inverseMaps 4) record021_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record021_frame004_links_0000 record021_frame004_links_0064)
theorem record021_frame004_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 4 :=
  of_group record021 4 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0146
    Papers.RationalityTen.SharedFrameCatalogue.group0146_facts record021_frame004_indices record021_frame004_graph record021_frame004_links
def record021_frame005_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0226.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0226.count (({ width := 8, code := 0x807d7a797877767574716e6d6c6b686766656261605f5e5d5c5b5a5956555453504f4e4d4a494847464544434241403f3e3d3c3b3837363534333231302f2e2d2c2b2a2928272625242322211f1e1d1b1a19171615141312100f0e0c0b0a090806050403020100 } : Fields).get c.val)
theorem record021_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0226.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0226.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0226.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record021_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0226.localPairCheck (smallEmbedding record021) (record021.maps 5)
      (record021.inverseMaps 5) record021_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record021_frame005_links_0000 record021_frame005_links_0064)
theorem record021_frame005_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 5 :=
  of_group record021 5 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0226
    Papers.RationalityTen.SharedFrameCatalogue.group0226_facts record021_frame005_indices record021_frame005_graph record021_frame005_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (Fin.cases (record021_frame004_supported hcells) (Fin.cases (record021_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5d6b15602974e09a525a4948b90f20a3ec568610a611c1c81500def3d87a6f3de6bc976cec9cab9170ad6daab4b682bf97d2ef5d8b896eac757aab53fa7a4e09ad2723744686909a063fe7e4f81ec3c6720dd1b23105f4bc16e2b84cc9411f230430839011f83e0788ec1ce384630c01762d8588820d21582a84f09c0e41c02f05a0a8120230420740e01902e0500780e0160200380400600800800 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcdf60db0056c0a7d53327c13d09c64da26a532e92c45a228112287d42ca118fba7c73d89e98f3c7963b69da0e3c7123789a5cd0c67a33497f0bf05d92e89708b745962bd1594a0c4fb274137495c48423011448844192088fc47be3d51e18e2c6d636217b0b845aa2c0152892446a22310807ac3be1ce0e106e43501970c305d824210e08003d01ce09403801700b605502a00e407002f01680a8048023010807403801900b805001e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x3966e4da5a231c62cbc5782ec5ceb95712c855ea9951a9f522a2d37a694ca9893025f4a69451f23b46686d0aa10416794f19dc3b274ce89c63746d0cb99531a62cbc16c2c657cae1532a052ca214227a4b49292120c3ec7c8f31d4350678cb1923045d8b51662b8558a814e2904808d11421c4206e0c0140278490900e41c02f05a0a8120230420740e01902e0500780e0160200380400600800800 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79dd9d799699297f93392a91e9118a689a88887d86e85f7f77927827717627387246c76b46a269869469067466d63362f6195d05c75bd5af54c54453652c5215144bd46f4624544464224123c63b73a839c39538837d37936b35e35034331f3123042f42e72a02942842732652091fa1e81da1cd1b91ad19f1901831721641561460fe0f20e70db0ce06f06e05a05905305203903802402301d01c01a01901801701501400f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2e49714b845b2ad81612b00571aa254faa7253327bd3d09c44da269d32e92c459228111e87d42e2118fba7c73d89e98f3c7963b69da0e3c7123789a5cd0c67a33497f4bf05dd2e89718b7456528513ec9d84dd26092b88c045122110c484441820890047dc3df1e90f0c73438b1bd0dac6c43061790b845a22c012d892446a22310807b43be1d00e106e43541970c305d824211008003d01ce07103801700b605502a00e4070024011807403801a00c806002e01500a003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x130a5fcbd9712de4d4999291b634c658bb0e21bc2d8510960fbee770ec5d73a7734e4db53616bad61aab53696d2595328644c097eaf95e6b35662c457cae95a28e4c49692ba5449291112a1e43685909a0f418820fe1f73e47a0eb1d0396704dd99f32c640c61842a65289f93626649c9011c22c440849011f43c45d0b115027c4b0610c01382684708c0dc1b0240460740e01a0320600b81502803c0700c0160200380400600800800 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x536974aa4d228f46a2d128742a0ce26f3499cca63309348e411d8cc5a1f0c8441a09038140600ff7f3f5f8fb7d3c5e0ed763add4e96fb71b2d66933d90c560af572b4582b956a953a9546a14fa753694482351487401f8f8793b1c4dc6b34198c6602e96caa5227930923c1d8d0662d160a04e200f86430160a85026110803c1c0c058200e04018080200 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
def record023_frame005_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0149.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0149.count (({ width := 9, code := 0x4ce6531984be5d2d964ae55299447e3d1b8d466311786c2a0f04803f5ecf377bb5d8eb753a5d0e773395c8e371365b0d56a34da4d163b1182be5d2dd60ad54a9948a250279389a4c259289248239188641a00fa7a399c4de6c34990c25e2d964ae542893c9246219007a351a0b85a2713094481e0e85c2c150a04c24110803c1c0c058200e04018080200 } : Fields).get c.val)
theorem record023_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record023) (record023.maps 5)
      (record023.inverseMaps 5) record023_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame005_links_0000 record023_frame005_links_0064)
theorem record023_frame005_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 5 :=
  of_group record023 5 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0149
    Papers.RationalityTen.SharedFrameCatalogue.group0149_facts record023_frame005_indices record023_frame005_graph record023_frame005_links
def record023_frame006_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0229.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0229.count (({ width := 9, code := 0x3bddced763add4e97439dcce572381bedd6e36db4d96ab4da2cf6632990c661b0982c05faf97abc5dae972b85bacd64b057ab95aac5429948a24fa7536994b25124904723114884321104803f1f0f474389b8d6683097cba5a2b9489e4c2491c8a421f8f46e34190c05c291409c4c211007c3c1d0e05c2c150a04c24110803c1c0c058200e04018080200 } : Fields).get c.val)
theorem record023_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0229.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (smallEmbedding record023) (record023.maps 6)
      (record023.inverseMaps 6) record023_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame006_links_0000 record023_frame006_links_0064)
theorem record023_frame006_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 6 :=
  of_group record023 6 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0229
    Papers.RationalityTen.SharedFrameCatalogue.group0229_facts record023_frame006_indices record023_frame006_graph record023_frame006_links
def record023_frame007_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0127.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0127.count (({ width := 9, code := 0x66f2f94c7e371589c3e02ff7ebedd2e771b7dbadb66ae56ab156aa54a9548a3512813d9c4da6732984a6512793476391a8c45e2d0f82c0e02ff7ebede6f177ba9c8dc6b35198c762b0d7aba5bacd5ea44fa71329644a1d06813f9ecf075391c0d86a34190b056299409a3e1e8d06631180a04e1e0e86c34180b8582a130903c1c0c058200e04018080200 } : Fields).get c.val)
theorem record023_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record023) (record023.maps 7) (record023.inverseMaps 7) record023_frame007_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record023) (record023.maps 7) (record023.inverseMaps 7) record023_frame007_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record023) (record023.maps 7)
      (record023.inverseMaps 7) record023_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame007_links_0000 record023_frame007_links_0064)
theorem record023_frame007_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 7 :=
  of_group record023 7 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0127
    Papers.RationalityTen.SharedFrameCatalogue.group0127_facts record023_frame007_indices record023_frame007_graph record023_frame007_links
def record023_frame008_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32e1946c9161ab07971ab7a59faac953ca8a53aa7713949a44c9a6012da8e743c21990a884440e2028f6c7a63ca9e10ede75d3809ba8cb264630595f8ad45562a092a092c47022f91308723b31a20cc86403101740b58504272130895449c24511f08e4460229111086c40e2000fc87c83d81c90e006e43641ab0c185f02e816d0b385602a214a0a184f426a12e09404841fc0f607783a41c407103801700b605502a00e4070024011807403801a00c806002e01500a003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record023_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 8) (record023.inverseMaps 8) record023_frame008_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 8) (record023.inverseMaps 8) record023_frame008_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 8)
      (record023.inverseMaps 8) record023_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame008_links_0000 record023_frame008_links_0064)
theorem record023_frame008_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 8 :=
  of_group record023 8 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame008_indices record023_frame008_graph record023_frame008_links
def record023_frame009_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x62d62a6266146115e25de5d059a58f58957c5395315245185115064cb49148547a46e45644740f4063fb3f43f13ed3dc3d93a93a539735f35a34e3482ff2fa2ea2e32d72cf29225524c23f23721b20e1d61cd1c21bb1b91b51b01ac1a61a019a19418618017b17617115715214d14714112511f1171121101091040ff0fa0f60ef0e90e50e00c50bf0b90b50b106a06905505404e04d03903802402301d01c01a01901801701501400f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record023_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record023) (record023.maps 9) (record023.inverseMaps 9) record023_frame009_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record023) (record023.maps 9) (record023.inverseMaps 9) record023_frame009_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record023) (record023.maps 9)
      (record023.inverseMaps 9) record023_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame009_links_0000 record023_frame009_links_0064)
theorem record023_frame009_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 9 :=
  of_group record023 9 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record023_frame009_indices record023_frame009_graph record023_frame009_links
def record023_frame010_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x69769368b67667163d63a6255e95e25d95d158d58757456b5625595254e94e14da4d04bd4af47a46e46445d45745443c4374034003eb3ae3a63a039935334d33933032a3212eb2ae2a429e29628327523d23322a22121921220e2091ff1f81f01e91d81cf1c71be1b919818e18617d17514f14a14113813212712111b11511010c1071010f90da0d40cf0c90c106f06e05a05905305203903802402301d01c01a01901801701501400f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record023_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record023) (record023.maps 10) (record023.inverseMaps 10) record023_frame010_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record023) (record023.maps 10) (record023.inverseMaps 10) record023_frame010_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record023) (record023.maps 10)
      (record023.inverseMaps 10) record023_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame010_links_0000 record023_frame010_links_0064)
theorem record023_frame010_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 10 :=
  of_group record023 10 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record023_frame010_indices record023_frame010_graph record023_frame010_links
def record023_frame011_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x20881a05812037f1fb7e9f47cdf27c5e5791df775db765d06e9b66c9ae6a5a5661936358a62187619855f97d5e9725c16e5b15855d53549515414a4f1384d1304a9254651543d0a419013f4fa3d8f33c0ed3a0e5388df370d032cc730cbf2b8ab2a4a4278962488e228872107f1e47619c621785a158400fc360d42f0b82a0a42007c19060160541404c110400f0380c02c0801c0400c0200400 } : Fields).get c.val)
theorem record023_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record023) (record023.maps 11) (record023.inverseMaps 11) record023_frame011_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record023) (record023.maps 11) (record023.inverseMaps 11) record023_frame011_indices (Fin.ofNat record023.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record023_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record023) (record023.maps 11)
      (record023.inverseMaps 11) record023_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record023_frame011_links_0000 record023_frame011_links_0064)
theorem record023_frame011_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 11 :=
  of_group record023 11 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record023_frame011_indices record023_frame011_graph record023_frame011_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (Fin.cases (record023_frame005_supported hcells) (Fin.cases (record023_frame006_supported hcells) (Fin.cases (record023_frame007_supported hcells) (Fin.cases (record023_frame008_supported hcells) (Fin.cases (record023_frame009_supported hcells) (Fin.cases (record023_frame010_supported hcells) (Fin.cases (record023_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
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
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe406e5b70da7ecb7627307181cc065e8aefd736b895bf2dc56c6aee56daa394f6a4b51da8d536298b4a624991fc8f645c20f90607fe3f81f9cf4a78d3ac9d04e6272538b9aa4d2c64831a9814bf05f32c11588a5a50d27793a497245a22810ac84241a1e68e746fa36f19e8c7461e2f61780ae047a2030fd07182ee16b0a304e824c10a07c03a41760b603781ac0c805f02d81540a803701980b004e02300e8070032017009804801e00e005002000e0050018008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x3901c26e056f23759b9adc26db363db02d636aab52da7ed3267e3331952c96631b10185ac0f6042df95c2ac9540a9a5476a364d7a64129492b47ea3e1164897429a0f50708133fe9fe0fd07323911ad4d4668c33f1950c8462b30e9810bf45f22ca1614ade56229f94c0a3450d27c93c09d24c224711a88c444d21d90cc83c41b1d98e846fe3531a08c7c60a2f81788ac851225b12408ec44220e10087e83841a00bb859c2ba14609b04b024c10807e83ac1b80d203a81bc0d6066030017009804601d80d806402c013808c0160080038014004001 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record026_frame001_links_0000 (interval_append _ 64 128 131 record026_frame001_links_0064 record026_frame001_links_0128))
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe406e6b4fd98cca062eb0dd81cc065e62e596f6b6e5b1abc5522a4a51da8d533693648623f91ec8bf447a0f90607fe3f81f9cf4a78d3ac9d04e6272538b9a78d0063d30f97e0be65822b114b4a1a4ef27492d092246822d114087242b21090687cc3d11d48e246de3491948c3c60c2f61780ad851e23d10187e83941a10b584e824c10707c03a410c08404001f80de06b02f816c0aa05401e80dc06602c013808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x84a81f7d27a179678077575f7587427307177056f96c76926676496405fc5c75ac59158356f56154553e52952251c5034fd4e64df4d04bb4a646445442d4173e43dc39c38836234c31a30c2f72e92d82d02c92bd2b62b02ab29028826e25724722d2152041f91dd1d31ba1af18515f15813d12c10c0e60d80c80c40c108408308007e06f06b05f05b05505403d03703302c02702302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
def record027_frame003_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x544a553fe6a4cc96f2ae4bc909051d631c5a8ad0de0d4047f0fd1e43ad742e59c73826f0d85ad346682cf193320620c2980af75dab095daa3532a053f2504868c112a124167ecf81e13b6754e49c137a6e0d39a0322610be96f2c856cac14d2904e49891b20a4087a0e71a63045d8b115c2a83d0780ea1d0338640b415c288500760d81902c04e08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record027_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record027_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record027) (record027.maps 3)
      (record027.inverseMaps 3) record027_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record027_frame003_links_0000 record027_frame003_links_0064)
theorem record027_frame003_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 3 :=
  of_group record027 3 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record027_frame003_indices record027_frame003_graph record027_frame003_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (Fin.cases (record027_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1c80dcd69fb319940c5d61bb03980cbd15cdadf96e2b6351da8d51fc8f645fa23d07c8303ff1fc0fce7dc3cf1e34ea47413971c88e2e6ac34f1a00c9663d30f9810bf05f32c115bcac452d28d14349f24ef27492d092246822d114087242b21090687c83d11d58e2c6de34b1958c3c60a2f61780ad851e23d10187e83941a10b584e824c10707c03a40de06b02f816c0aa054027013009004601e80dc06602c013808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x2a252a9ff352664b795725e484848ef1a22fc567f0fd1cb38e704de1b0b5a68cd059e339648c818730a5f8bc976ac7584aed54aa3532a3540a7e4a092521a304548950ea124167ecf81e13b6754e49c137a6e0d31a0324614be9702ca56cab94d2904e49891b20a4087a0e71a63045d8b115c2a8338640b415c28850094120228440760d81902c04e08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame002_links_0000 record028_frame002_links_0064)
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe406e6b63dac6d4b69fb4c9818c065bfadb95f4ae65632a6950ca6652528f546a9c54cda58126c90c47fa3d917c88c41e20c0ff87f03f39e94f1a7593a09cc4e4a71734f1a00c7a61f2fc17ccb5a55628093b89d24b524a914084241a1da0e7c71237d1aa0cfc65231d1830bdc5e02b5145896c49423d11088404061fa0e4868c2d213809304241ec0e9049023810807e02f816c0aa05401e80dc066028013809004601f00e807002e012007002c0100070018008002000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xb7e5b2ad85628ad055baa25506a72536288d4209c14d225b12be94949e23b11ac8093f71ec4f2278b3b39c98dcc6d63661af0d046653189880bc25d02e516e4b0c56a29c14a897c4b122110688243eb1e78ef47123691b10c9c62a2f81728b5c5882a314009b848c23511188403e41e20ea871434a1850ba8538282131090842c1fc094047821810807103101640aa05402381140680250100074038013009003c01c0080038008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xcac631b14d7a4b655a12bf95e6ad956629e94d09f94eb264930e96d4b024391f88a844fa2310908363f51df4e3c70837f9ba0d3e67d31d98a8b925b32d5164ca94528273135493849723510cc8383e41db0e4c6a832918c8b6058a2ad14d8a384f825611d88b04161ff0f887903941b80d586642e61580a484a023810e08083d41de094047821810807103101640aa05402381140680250100074038013009003c01c0080038008002000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x74273172b6f96c66b569568e67f67b64c64060d5fb5db5d75ca5c359158653852f51c5034fd4de4a647446646045442a4133e73dc3a839c39838a35e34931a30f2dd2d82ab29028826e2572472212092041dd1d31c41bd1b71af19c18e18516d16815f15814513d13612f11c10c1060ed0e60e10d80cc0c809208d08408307106205905505404704503402502001d01c01301200f00e008007002001000 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
def record030_frame004_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x4a793d27241c678bb1262343c8710860dbf87e0f81eebd279cec5d63656b2d199b333650c457daf05d8b9164ac055eaa5462824fe9d52da5447e8e9042043a8728e19b134c674c417c2f2598b195e2b0548a693f2664b08e918222434849041fc3e0740db1aa318600ba16c2c0558840fe1d83a8670b21442684c086108198250400740e01302403c0700800e00800800 } : Fields).get c.val)
theorem record030_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record030_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record030) (record030.maps 4)
      (record030.inverseMaps 4) record030_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record030_frame004_links_0000 record030_frame004_links_0064)
theorem record030_frame004_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 4 :=
  of_group record030 4 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record030_frame004_indices record030_frame004_graph record030_frame004_links
def record030_frame005_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x53ba5d4a689cf59d73666accc98d29a4f4808ef19a314598ab0da173e57aef01d53a6736e15b4b5a6b0d3d9bb2c62cc457bae95ccb7562aba54ca8134a6646485d071fa3d0770e29b535a65cc79872fa5d8b715e29e5109992a2424688a90c20e404790e91c4354680ca1882f45b8861061ec3d06a0b814c2784e08810c1a0250400740e01302403c0700800e00800800 } : Fields).get c.val)
theorem record030_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record030_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record030) (record030.maps 5)
      (record030.inverseMaps 5) record030_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record030_frame005_links_0000 record030_frame005_links_0064)
theorem record030_frame005_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 5 :=
  of_group record030 5 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record030_frame005_indices record030_frame005_graph record030_frame005_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (Fin.cases (record030_frame004_supported hcells) (Fin.cases (record030_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record030_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105
