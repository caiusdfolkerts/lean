module
prelude
public import GraphInputsRow31Part00173Data
public import RawFrameSupport
public import SharedFrameGroups009Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups012Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c74e246b0b321970ca464eb25d91ac8864131e970cae45672b0156eab3555aa8953a9bf4b2254127692d48c242916289d44421e90ca857426a11107c8364179df4e5e6d334299f0cea66f3341984cb0651326190cc7e58b2bc9544a8653228c141c9f84ec26212d894a48b23d11bc8ca46022e11588a237c1a78cc06162fe16e8ab851e26a12e88f046422a111887042a1b70d0862c2f81690ab8514260108079834813c09403e01e40e406f02e816c0b405802b015408804302080e8072037015009804a023011008404001e00e8058026010007803801a00b00500240100050018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record000_frame001_links_0000 (interval_append _ 64 128 142 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x8ab136224398630aa1442584507e01bec7c2f49e6bc9788f01deba6724dedb9b6f6d2d8daeb596a2d199fb3865ac898f31361cc217e2f75d6b9d63aa9538a3543a844fe9e93ba6a4b492d22a4347e8ed1ba3445e8991021b422821031fc3f27d0f41e63b8764da99e310600be1772e65bcb59642b2540a4932248474868fd1f03c4758e51a8328620b914c2784b08e112210320630c41843005f0b21602b0530a21401c03706a0cc190310560a8140250460880b0150260400700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame001_links_0000 (interval_append _ 64 128 148 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x71db5edaa0d36688b42da08cfc67b33b97a2b695902b1155ea9c544a9dd4cc9fd4da256128693048ea42d1f48ef47423851b48d3465230d17c8b545822a514089b449222cef871636a9a04ce265e32618e0c505c12c014b0a3850927b938c9a64c826092e89664ad252127493048f245120c8f647723791a47d43911960c606062f016c8b1c5722a914c8a284f424c11688744001d60e306d834e1970b4852827411d07b83c01d20e206d83500e407103781b00d406903181880c005d02d816807403901b80d006403101580a8050025011808802c015009804001c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame002_links_0000 (interval_append _ 64 128 148 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xabb5329fd34a434768cd16a274426acbc94920e3f4788e71be354548710760ac1281901a01c007f4fcdf6be77bef65eabcb790f05dc3b4752e95acb3b646c0d7eaf65e0bb173acb55ea5546a885049f13ca764e49b5342634b69592aa4b4949111d23945e8ad011e03726c0d49a032c640c51842f85d4b615a29c5109a92023444c861051de3746b0c816a2bc540a11362583786e0da1a8340670c41842f85d0b61681d03906e0d0190310560a8140250460880b0150260400700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame003_links_0000 (interval_append _ 64 128 148 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7cb3a3dc36dc26a4b4d1a38d02676b34d73eb2a56ca9d14bca4c51c288d4209a24aba3e91cc8d3460a2b113488b43ca19d0aa845415a0690207f63f61f70f867ba3d11e40cd65f62d29500a5451828213bc9b846e2118f1876439f1c68de06cc3571a28ccc64231117b8b985b82c215c0aa051e28613709704642140f987ac3c81de0eb07403921c20dd86d035a1980c5060c2ea1600ac8548296144097848423410c07a83b81ce0e006c834c0e407103781b00d406903181880c005d02d816807403901b80d006403101580a8050025011808802c015009804001c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame004_links_0000 (interval_append _ 64 128 148 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xb7f6a2c8d85ae15aeb255fab5546894f99c52fa5acb19552924ec848df13a22c418750d216c278470660b40c806fedfcbf07daf9dec3d478aefdc236168ecc193b21638c51882f05aaaf95bab1556a914fa99522a2d41a804ea9a9342594a893521a4046a8c4fe9db3706b0d39a0330644c59852f85d0b615828a4f49591722642c828ff1dc38c6e0d117c2e0590ab14c2843586a0d2198320630ba1702d0570aa1501c83806c0d0190310560a8140250460880b0150260400700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame005_links_0000 (interval_append _ 64 128 148 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8ba87f85f84882a82481d81681180979474e7216ed6e36d26c76bb6af65d62b5f15e55d15c45b55a559858f58757f57756d56555f55454d54553b53552b5244b14634313f73eb3d73ca3bb3ab3603332ff2f52e42d92cd2c12b52ac2a429c29428a28227c27126a26225825224824121a1fe1df1d71d01ca1c21bd1b71b01a81a119918117116915b14513e13612f12710f0ff0f70e90d40d00cc0c80c40c007207106f06c06a06906306206005d05b05a03a03903703403203102b02a02802502302201601501301000e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame006_links_0000 (interval_append _ 64 128 148 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x83e8037e27c67a379878f78777f7747156f36dc6b06a569f69468d6836586326025f25ea5de5d15c45bd5b65a75a159258457b57656a56555a54954252f5264cb49846c44443742d42241440a3df3ba3a539c39338c38037a37336535b34f34a33a32c32731530d3032f82f32e32dc2a727924723b23222a22021820f2071fb1f11e71c91ba1ad19817917116415a15213111a10e0fd0e20da0d10c80c00b806f06e06c06906706606005f05d05a05805703903803603303103002b02a02802502302201601501301000e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record001_frame007_links_0000 (interval_append _ 64 128 148 record001_frame007_links_0064 record001_frame007_links_0128))
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xaf55e2ba56ead3596aed5aaa752aa25099a333663cc297d2da59cac9472763245d8ab13e24c418790d61542483f0620840a808ff1fbbf07caf7dee3d87a8f41e63926c0d75a7349686cf99c32f5bab6161abe572acd54a9e5249ed3b2724d29792aa4647c8e11b22e450774ec1c13786e0d79a4336630c29702d6598b01562964f89c13625c4a09190f2124007e0f51d83806c8d519c320610bb16e2c0550a71442804d09712c2404508710c1d4348660ca1682b85607e0d81a8340640c41382604a08c1101201802c0480800c01401802 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 152 :=
  interval_of_check _ 128 24 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 152 record002_frame001_links_0000 (interval_append _ 64 128 152 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xbddeaf176ba5cae16fb6daad15fab552a550a75329749a351277399bcd66731984ba57299449a49229047a3b1b8c45a2b1489c4a230980c01f4f87b3d5e6ef7238dbadb6cb61acd266b198ac460af978b75aacd64b057299489d4e26d309549a391a8742a0d04803e1dcea74391c0de6933994c8622f164ae562a148a04e2692c924823918823e1e8f06e34198c85a2a1489042200e86832180b0542411080381a0a048200c050200c0200 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 152 :=
  interval_of_check _ 128 24 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 152 record002_frame002_links_0000 (interval_append _ 64 128 152 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xbddeaf176ba5cae16fb6daad15fab552a550a75329749a351277399bcd66731984ba57299449a49229047a3b1b8c45a2b1489c4a230980c01f4f87b3d5e6ef7238dbadb6cb61acd266b198ac460af978b75aacd64b057299489d4e26d309549a391a8742a0d04803e1dcea74391c0de6933994c8622f164ae562a148a04e2692c924823918823e1e8f06e34198c85a2a1489042200e86832180b0542411080381a0a048200c050200c0200 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 152 :=
  interval_of_check _ 128 24 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 152 record002_frame003_links_0000 (interval_append _ 64 128 152 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c3cd5565e32e1962caa64c323d910c7f63dae095c0adb563ab01574ab2555aa955369c54d5256928092d48b241d1ee8a7446a1e90c6854425a11107e83741799f0cea66f3341984cb0653326190cc7a5852bc95b0abe53129314609f24ec26f934894849924591b08ca46022d915c8a237b1b68cfc66031c1870bf85d62cc14f0a3c4f626d12e892846222a112087042a2060d206382f81670ab04b82480f107383481840b904e02480f006e02f01740b405902c0154094044020810007403701b00a004c025012008804202000f8074024011008003801a00c00580240100060028008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame001_links_0000 (interval_append _ 64 128 142 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x7266ea6ad6aa6a269b68467966f65d65b6125d55d25bb5b45ac5a159758f57654353d51f5195125074fe4fa4db4d54ce4c44bc4b54ae4a94a14984094043f73f13e43db3d43cb3b63a935c35434b34332a32431a3012f92f12e92d32cc2bf2a729d29128727f27021e2161fc1f41ec1e61dc1cc1bb1a519d19518e18117115f15314a13d13212910a1040fd0f60f00de0d70bf0ba0ae0a509f08e08607406c05c05b05805705605304a04404104003a03703602802602502402202102001f01d01201101000e00d00c00b009008006005002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame002_links_0000 (interval_append _ 64 128 142 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x2995019b73626a4ce9832ea59cab9511c225c488770d618c2a84707e09be97c6f21e0bb9762ea5d2389704de9b8b6b6ccd89af3586a4bb974ae25b8b55672cb58aaf15ba834f89e93b2664c0961262464828ed1321e42a814ff1f83e67c0f41b135265cc89893025e0b79602a8540a51442784d09612624446c8b1101e63b4748e21b8338648b21622984f09a10c204370690b41642b0550a81442404207e0f81c03506809c128240460841001f03c070090110200380680c0160240400600a00800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame003_links_0000 (interval_append _ 64 128 142 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb14acda8ca87a80a78a59a3fa32a1aa1599b94293e92091390c8f58e88df8bf8568457fd7e07cf7b97a579b75673b72770d6fd6eb6d96cd6b76a05d95d25c95bf5b159959058356b55d5004fa4ef4e44b94ac49e47d47546d4604324254153f23e43d63c53ba3a633732d3052f52e42d92cd2bb2a02752672572492392252071f81eb1d91cb1c218417316515314511910a0d80cd0b40a60a309608c07606c05c05b05805705605304a04404104003a03703602802602502402202102001f01d01201101000e00d00c00b009008006005002001000 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame004_links_0000 (interval_append _ 64 128 142 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x35367ccad95329651c9190b2063ac6f7cadddb8b5b6a6d35a0b3b66ac8d48a8345a824f99d33726acaa9372463ec708d11923145a8a4f29e33c3780ef1dabb275eea5d1b576a8d35a232663cc557f2f85e6bb1652c3578a894da9852aa4545a3546086d092043fa7c8f49d83866f0d61a533c644bf17a2ee5bcb49632644948d1091f83846c8b515a26c4908e1041f0348620a814c2804f09c12c2203f07a0f01b8350680a0130250480881082003e074090110200380680c0160240400600a00800800 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame005_links_0000 (interval_append _ 64 128 142 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x1cc38a6f2dd9ba36d6c8d79ab34e69ace193b24632c618930b610c097a2de5b6b25632c2574ad158a98528a3942a7f4f49d138a6b4c68810ea17424835032053fe7ccf61cd39471ce01b33606acce19b332650c19802f65bcb51662c4584ad13a26e4a49312023c460871081f03d4780ed1ce3806b8d21a2328638c315e2b0548a614625c498861062003e87b0e41b43205f0a41442704d098124230440821001d03706c0a0130250480881082003e074090110200380680c0160240400600a00800800 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame006_links_0000 (interval_append _ 64 128 142 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x22b43882f05608c09804fe5f9bec7d4ef9d33a4732e5dc8b88708dfdba35a6aad059db37660ca993b1361cc2580afc5f0bcd782e95c69c1352634ba95d2724c48e8fd1d20c41481d009f43e07a4ee1d93a6738df1b9366694d099c32e654c79602ba540a514227e4dc979272384688890e2103f47a8f11da394718df190314610be1762c45609e134254448830f01cc328610ac154290510a01342103e0760e81b033064098120230440800f81e03a06c090110200380680c0160240400600a00800800 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame007_links_0000 (interval_append _ 64 128 142 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8077c279178c77175f7586f76a869f6946896706496405ed5e45c95be5b559158357b55a55454d54553e52952251c4a444d44343842e40e3e43dc38037635734d34131a30c3062e52df2d82d02c92b62b02ab23c23222421a20c1dd1d31cb1c31bc1a71a119718515f15814b13512e12712111710c0e60d80c40c108e08d08207c06f06d06c06b05f05e05d05b05905805505404a04403703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame001_links_0000 (interval_append _ 64 128 130 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7056c76986926766676625f95b65b25ab5a459358458153a5305135094fd4e84e14d94af4a649c49048a47747146c3f83ac3a83a339e38e38037d33132b31430c3032f32ec2e72c42bd2b52ac2a829a29729422421920c2031fc1da1d51cc1c11b419c19618f17d16616215913d13212611e1131070e60dc0c00ba08a08907c07606d06b06a06905d05c05b05905705605305204804203703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame002_links_0000 (interval_append _ 64 128 130 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0948.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0948.count (({ width := 9, code := 0x26d359a4ce612e96c8233188b456251087c220f0481c05fefe7ebe5f0f77abd1e4f178399bede6e36db0d66ab399aca64b1d8ac461afd7cbd5dae96eb65aa7d3a9a4ba511e8d452210a82401f4f072381b4d6683298cc05d2b14c9c4c2110474391c0dc6c351a0cc6431180bc5c2d13094482311084401f0f074381b0d0642610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame003_links_0000 (interval_append _ 64 128 130 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0948
    Papers.RationalityTen.SharedFrameCatalogue.group0948_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb1fad9a99a86a54a24a0e99c94493d9329299018d48c584d84581c8097f47c17a679b75273b7277106ff6c56b46a26375de5d85cf5c659a56e5635014fa4da4cc4ba49247e4754384254154013f43c43b73a832d3203133052f52bc2aa2a02962862582492392191da1cd1c21a019118217316515511b0fe0da0ce08a08907e07a06d06b06a06905d05c05b05905705605305204a04403703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame004_links_0000 (interval_append _ 64 128 130 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x21942382703e03bfd7eef4dd8bad74ce75c7b796e8d39a533b668cb18c30f614be579aec5ccb85682cb58ea5137a6b4ca9752723a46a831041f83e47acec9d03966e8da1ae35068cc998f31657cac1512945049592824c4908f11222042c800e61c4378698d1194324618bc14a268468890e01bc350680bc1742e05b0a61482884f09a130248480840f0190310600bc1382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame005_links_0000 (interval_append _ 64 128 130 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x22743e85d0a20cc0b80cf81e33c3780ef5d83a273edd9b93606b2d4da0b3a66cc6589b0d608bf9772e85c4acd4aa9251ea2d3f2714dc91d22a354628b110219430800fd1f63e07b0f01dd3b465cc898930e608b49642c2574ab94127c4ec9711b22c4447c8f31d63986f8d617e2d05089a1001fc3a0710d219c330650b61682c8570aa1502885008c1041b8350680cc1382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame006_links_0000 (interval_append _ 64 128 130 record004_frame006_links_0064 record004_frame006_links_0128))
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0512.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0512.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0512.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0512.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0512.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0512.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0512.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame007_links_0000 (interval_append _ 64 128 130 record004_frame007_links_0064 record004_frame007_links_0128))
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0512
    Papers.RationalityTen.SharedFrameCatalogue.group0512_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f42e986de3675a60ce66662e615aeac5558aa754b6a22509255928c90c47d239115e89844420c903e80d3fc1fa0f687a63ca9990b465912be95a4a4e4ee26f10888243d81e30ec06f63641aa0bf85d62d91620ad0500272130883c4102010fd07cc3aa1ce0e487083761a40cf866031216d0b3858029614409e04d825e12708583f81d00e2048023c10407c03781b40d806b02f81780ba05b02c81600aa054025011006e03501a00cc04e026012808c04202000e807002c013009004402000f007003001600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame008_links_0000 (interval_append _ 64 128 130 record004_frame008_links_0064 record004_frame008_links_0128))
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x2744d596d2ca50c9391b16e1642884907e083fd7eeefddd3ab748e79c437c6ecd69a9b4b686ced95b2563cbb55c2b355eaa14ba7e4ee9112023345c8a10a20d4107b0f29dd3a8734de1b636060cbf1782e45b0ae1572a6534a413926c4c09090c20c400790ed1cc38c6e8d517c2cc538a10f41e43706a0c01782e85c0a814c2905009c134250490820f41a0320620c01382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame009_links_0000 (interval_append _ 64 128 130 record004_frame009_links_0064 record004_frame009_links_0128))
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1040.count (({ width := 11, code := 0x20ec1181100dfb3ee7d4ec5c6b8a70ee09bab686caced9bb2c652c8d8cb14622bfd7c2f35d6b9d6bad45a0a513a2714dc9a52d24f4988890f211418810fd1f43e277ced1d73a2738df1ba36e5ecba96f2d0590a61482864f49b92824647c881021fc3e8768e51bc368690cb16a2b84d8980fc1f43806c0ca18c310610ac1542a0520a013c2604b0820f41b0340660c81382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame010_links_0000 (interval_append _ 64 128 130 record004_frame010_links_0064 record004_frame010_links_0128))
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1040
    Papers.RationalityTen.SharedFrameCatalogue.group1040_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0926.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0926.count (({ width := 9, code := 0x2472290c823b1b8d4360d058240e00fe7ebd9eaf3793c1dced763a5d0e772b91c4e17034d98cb653258cc461af176b95c2d968b3592bd5cad55aa950a753251248f462250882401f8f6783b1ccdc6a34198c8612f170b2562893896492110474391c0dc6c351a0cc6431180bc5c2d13094482311084401f0f074381b0d0642610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0926.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame011_links_0000 (interval_append _ 64 128 130 record004_frame011_links_0064 record004_frame011_links_0128))
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0926
    Papers.RationalityTen.SharedFrameCatalogue.group0926_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0947.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0947.count (({ width := 8, code := 0xc6c5c4c3c2c1c0bcb8b7b6b5b4b3b2aeadacabaaa9a8a7a6a5a4a3a2a1a09f9b979695949392918d8c8b8a898887868584838281807f7e7573716f6d6a68666462605e5c595553514f4d4b494745413e3b393534302f2e2d2c2b2a292827262524231f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0947.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame012_links_0000 (interval_append _ 64 128 130 record004_frame012_links_0064 record004_frame012_links_0128))
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0947
    Papers.RationalityTen.SharedFrameCatalogue.group0947_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
def record004_frame013_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0910.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0910.count (({ width := 8, code := 0xc6c5c4c3c2c1c0bcb8b7b6b5b4b3b2aeadacabaaa9a8a7a6a5a4a3a2a1a09f9b979695949392918d8c8b8a898887868584838281807f7e7573716f6d6a68666462605e5c595553514f4d4b494745413e3b393534302f2e2d2c2b2a292827262524231f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0910.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 13)
      (record004.inverseMaps 13) record004_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame013_links_0000 (interval_append _ 64 128 130 record004_frame013_links_0064 record004_frame013_links_0128))
theorem record004_frame013_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 13 :=
  of_group record004 13 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0910
    Papers.RationalityTen.SharedFrameCatalogue.group0910_facts record004_frame013_indices record004_frame013_graph record004_frame013_links
def record004_frame014_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x71e6e46a669a6706476365e65a55a059958e57355554e4f84f24de4d24c84ac49c49546745944a43942f40d4063fb3ad36c36735e35933a31c3152bf2b92a229c28f27326325c22e21e2112001f61d41cd1c218b18718117c17715f15b15715414f13b13813212811211010c1000fb0f50f00ea0e40ce0c50b40b108208107807406806606506405805705605405205104e04d04704303703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record004_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 14)
      (record004.inverseMaps 14) record004_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame014_links_0000 (interval_append _ 64 128 130 record004_frame014_links_0064 record004_frame014_links_0128))
theorem record004_frame014_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 14 :=
  of_group record004 14 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record004_frame014_indices record004_frame014_graph record004_frame014_links
def record004_frame015_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x1e2bb6740e79c737c6f0d719f33d674cd59531a62ebc177ae25b8b5963ac0576a9550a9b528a394127d4f49791ca384648b10fa0d4167a8f49dd3b6758e39c237a69cd119d32a644c197f2f8524a293f2764d89111f23a4688a9062063f87a0e21c0370670ca18a3085e8b714a27c4988f0ec1d43606a0c017c2f05d0a41442804e09812c240470820fc198310600bc1382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record004_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record004) (record004.maps 15)
      (record004.inverseMaps 15) record004_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame015_links_0000 (interval_append _ 64 128 130 record004_frame015_links_0064 record004_frame015_links_0128))
theorem record004_frame015_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 15 :=
  of_group record004 15 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record004_frame015_indices record004_frame015_graph record004_frame015_links
def record004_frame016_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x21b42181f029fb3e87c6ed9cb39271ce21bdb6d6d2d09a0b36662cb18fb1962cbf97d2f55daba56dad55a0a7d422804f69e134a5b4ae8c11721e43285103a003fc7a0f21e23b475ce49c237c61cc097d2f25c8ac95329c530a293025c4ac8d9041fa3dc738e21ba3686a0ce1782c05009a0f41e43706b0c41802f85e0a814c2905009c134250490820f41a8330640c41382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record004_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record004) (record004.maps 16)
      (record004.inverseMaps 16) record004_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame016_links_0000 (interval_append _ 64 128 130 record004_frame016_links_0064 record004_frame016_links_0128))
theorem record004_frame016_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 16 :=
  of_group record004 16 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record004_frame016_indices record004_frame016_graph record004_frame016_links
def record004_frame017_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0503.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0503.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0503.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record004) (record004.maps 17)
      (record004.inverseMaps 17) record004_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame017_links_0000 (interval_append _ 64 128 130 record004_frame017_links_0064 record004_frame017_links_0128))
theorem record004_frame017_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 17 :=
  of_group record004 17 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0503
    Papers.RationalityTen.SharedFrameCatalogue.group0503_facts record004_frame017_indices record004_frame017_graph record004_frame017_links
def record004_frame018_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0511.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0511.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0511.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record004) (record004.maps 18)
      (record004.inverseMaps 18) record004_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame018_links_0000 (interval_append _ 64 128 130 record004_frame018_links_0064 record004_frame018_links_0128))
theorem record004_frame018_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 18 :=
  of_group record004 18 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0511
    Papers.RationalityTen.SharedFrameCatalogue.group0511_facts record004_frame018_indices record004_frame018_graph record004_frame018_links
def record004_frame019_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0498.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0498.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0498.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record004_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record004) (record004.maps 19)
      (record004.inverseMaps 19) record004_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record004_frame019_links_0000 (interval_append _ 64 128 130 record004_frame019_links_0064 record004_frame019_links_0128))
theorem record004_frame019_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 19 :=
  of_group record004 19 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0498
    Papers.RationalityTen.SharedFrameCatalogue.group0498_facts record004_frame019_indices record004_frame019_graph record004_frame019_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (Fin.cases (record004_frame013_supported hcells) (Fin.cases (record004_frame014_supported hcells) (Fin.cases (record004_frame015_supported hcells) (Fin.cases (record004_frame016_supported hcells) (Fin.cases (record004_frame017_supported hcells) (Fin.cases (record004_frame018_supported hcells) (Fin.cases (record004_frame019_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x33f19d8c8f6292a5d50ea2a4f6a6112fa9764afa52927c929491246922890d482a3a51c68dc3851be4d306582ba1584a9e51626f92f891047723311548864311f80f847a23051790b8054e27012788644101f70f307503841810b905882ac14f0a4050427412c09283f41ec0e3052824412008f04101b80da06c03181800be05e02e81700b205802b01540a804a01b00d406802b014009c04c025012008404001e00e807002c013009004402000f006002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36c5b3ad2a671ab6158aa61513251926491e472a2ad11085242120bd03e80d3fd1ed8f4e7952d21644a5a4f22090ff87d43b11bb8d5063c30e17d8bac5b22c614109cc4c220f10408043d41d50e486d035a1a50cf86603201740b7059c2c01590a9052c28813609784141fc0e9052824412008f04101b80da06c03181800be05e02e81700b205802b01540a804a01b00d406802b014009c04c025012008404001e00e807002c013009004402000f006002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xde5bab5968ab716c2bc5509ed3c2754d49852ea544a293525a484888e11b2333ac748db1a22ea5c8b79642b655ca714b28e514a113e2644c09690c2124187d8f21dc394710de1b83646a8c918e310608c017e2f85e8bb1742d0598b01422344608b1001b03586a0c21782e85c0b61682b8560a814c2904a06c0d41a02b05009c130250480841001e03a0700b0130240440800f01802c0480800e0180280400600800800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8fa86a50a2194593d9058d884583782a7f57bd79b76f76074f73b7277126c76b56a25df5d859f5724fa4ef4e44bb48e4754524444354254154033c63b83a832d3203132e52bc2a02752672592492392271e81db1cd1c21ba1ae1a019117316510b0fe0db09b08b08a08907e06c06b06a06105e05d05c05b05a05705605405305204a03603503402b02802702602502402102001e01d01c01601301201101000f00c00b009008007006005004003002001000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2fd97ccb8c5ac29654949f04e024bd2308ff462a2390ea8324102038ffc7ec3ed1e44efe76d3291910bdc5c129d949ca244e525d12948e246422b112487842e1fb0fa47ba35019d0c905ea2c815889e04da25f129091c4722000fa079c3ac1c60da86a03381850bc84902300eb052824412008f04101b80da06c03181800be05e02e81700b205802b01540a804a01b00d406802b014009c04c025012008404001e00e807002c013009004402000f006002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0601.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0601.count (({ width := 8, code := 0xaaa9a7a5a4a3a19f9c9b9a9896959492908f8e8b888786858482807d7c7b797776757371706f6c696867646362605e5d5c5a58575653504f4e4d4c4b4a4947464443403f3e3d3c3a393837343231302f2e2d2c2a292827262524211f1e1d1c1b1a191716151311100f0e0d0c0b09080706050403020100 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0601.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0601.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0601.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0601.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record005_frame006_links_0000 record005_frame006_links_0064)
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0601
    Papers.RationalityTen.SharedFrameCatalogue.group0601_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c48d6166432e1948c9d64bb23d910c8263d2e195c8adb56aab3958eac055baac9556aa254ea6fd3549764b2254128092d48c24291ee8c3458a27511a87a432a15d09684441f20d905e72f34299f0cea66f3341984cb0653326190cc7e58b2bc9544a865322931460a0e4fc276131096c4a524c922c8f446f23291808b84562288df06da35f1a78cfc66030e17f0b745982be1570a7851e26d12e88f046222a111887042a2060e606dc34218e0be05a42ae13007983480f807903901bc0bc05d02d81680b205802b015408804101d00dc04c025011808804202000f007402c013008804001e00e006803001600a004802000c0050018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame001_links_0000 (interval_append _ 64 128 154 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f44e926dcb67dab6d43699b4519f8cec666ae6d5b2ac855a2a81518a7752d2941476a1f509a56d28c90c47d23911a88c1455226911085242120b503e80d3fc1fa4fae7c63dc9e94f266672d29650b0056c2ac150ca4c51c28393ac9be4272090f6078c3b01d00e346ec3661aa0c7861c2f91758b645882b51518a4850a27112f885041e20810087e83e61e50ef07403921c20dd86d035a19f0cc062830217a0b985b02ca1600a58510278136097849c24210b07403540f807903901bc0bc05d02d81680b205802b015408804101d00dc04c025011808804202000f007402c013008804001e00e006803001600a004802000c0050018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame002_links_0000 (interval_append _ 64 128 154 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x37d6d4d65aaf4f698d29a3b44682cf784ee45c5b816eada5afb5168ece593b1f4c2925089ff3da764e39af346624a793b25244c808e71b230c5a8ab142253e2732e59c8b8b70ae01bcb746dad91b03015eab61672c5574ac55229d51e9cd352614ae9392123c4648ad13221436784ee1d539c718e01b035266cc918b3085f0bb1662be544a51462844f89d13524a4788b912218418810ea1862b83c8760e01b42e05b0b21602b8560a814c218400740dc130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame003_links_0000 (interval_append _ 64 128 154 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x199cc5c5fcafa1762ba05c9adf56d8b5f5a7aaf94b4a4d51d2885424a024f527893a49ba4daa50125e8ec46da31116a8a4446a2150ea8324102034ffc7ec3ec9f48f7c7a93ca1df4ed66c0329991cc6461d30717fcbce5e12e916e8b6c54a29d94089e84e426b93249724b225291c48c845422490f085842620b901c7f23e71ed8d846a033a1920c5460c2e816c8afc56229d14509e04da25212388c44442110ff87c83ca1d60d4067031e1850bc85b02c813007503200f807903901bc0bc05d02d81680b205802b015408804101d00dc04c025011808804202000f007402c013008804001e00e006803001600a004802000c0050018008002000 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame004_links_0000 (interval_append _ 64 128 154 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x71e6eb6c46bd6aa6a169b6906876816786165d65d25ce5c45bb5b25a259d59258057d53352b5074fd4f04e54d94c94c34bc49f49949048847f47346e46445945344643b3da39a39639238837e37336135d3543443412f72ef2c92bd2ad2a429a28d28728026225924d24624023723222821d2172071fe1c51c11bb1b41ae1a619618e17f17d17917216b16515514f14013c13813312e12712311410d1061000f90f20ed0df0c30b307b07807106e05d05c05a05905805705505404404103a03702602502302202102001e01d01601301101000f00e00d00c00b00a009008006005003002001000 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame005_links_0000 (interval_append _ 64 128 154 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb20ad5a97a87a6ca5fa56a3fa32a29a0f99e94693e93592c9209139008f58e88d18c685184581c8097f47e07cf7bc7a879b76f76074d73b7277107006eb6d96ca6b36a06395e05d95d25c95bf5b159959058356b5645064fa4da4cc4ba4ac49e48d4804754524444334254154013f53e43d63c93b63a633832d3203133052f52d92cd2ac2a029628627526724923921a2071f81e71d91cb1c21a019118217316515514611b0da0b407a07707006d05c05b05905805705605405304404103a03702602502302202102001e01d01601301101000f00e00d00c00b00a009008006005003002001000 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame006_links_0000 (interval_append _ 64 128 154 record006_frame006_links_0064 record006_frame006_links_0128))
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x355680cb59532764ac8f90b2063dc6d7d2dedb8b696c6d6da9b47682ced97b27516a0d26a3543e824f99d737e6acbb96728e4dc918ff1ce344648c3166294087a0f29e33c3780ef1dabb275eea5d2b5a6a8cf99a32763cc5584b015f0b896dacb586af156aa5536a614b2905168d91822844086d091fd3e477cec1d239670cde1a533c61cbf17a2ec5bcb496328e4f09812523442c7e8e316e26c3606a0ca18c2a0530a21402784e09812c1f83d06e0d4130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame007_links_0000 (interval_append _ 64 128 154 record006_frame007_links_0064 record006_frame007_links_0128))
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
def record006_frame008_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x24a4728a71422244087b0de1942e84efe1e5bc6786ef9debb8766ec5d5ba774add5b8b646b6d55a7b4767ece999b22638c4d873055f4bd576ae85cab816eaaa5049f53ca784e69c9352674c89792e22c44e85907a073fe7e0f71e93c674ce89c73806ecd89ac34667cce197328594b115d2b2550a814527c4d09812d24e48c8e91321a4087e0f71ea3cc788ed1be36c6b8d219630c5f8b01362483606a0c81842905109e1382684c0941241f03b06e0d4130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record006_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 8)
      (record006.inverseMaps 8) record006_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame008_links_0000 (interval_append _ 64 128 154 record006_frame008_links_0064 record006_frame008_links_0128))
theorem record006_frame008_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 8 :=
  of_group record006 8 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record006_frame008_indices record006_frame008_graph record006_frame008_links
def record006_frame009_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x227c3d85b0aa1141e8350520840c80ef85e3bc5782ef9ddbb775eeb5d4ba1740de1b93606b2d4da6b4767cced9b325640c5989b0d608bfd7c2f35e0b9d70ab452ca514828c512a153ea7c4f09c137a4948a8d518a2c45088d0e21a43081d021fc3f47d8f81ed3d2794f11dc3b266ccb99131261cc11762e4594b095d2ae53ca493e2764bc951262424688a9111f23cc758e61be358688bf1422403886f0d61a42d0590ae1582a8540a41442083f0740dc130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record006_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 9)
      (record006.inverseMaps 9) record006_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame009_links_0000 (interval_append _ 64 128 154 record006_frame009_links_0064 record006_frame009_links_0128))
theorem record006_frame009_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 9 :=
  of_group record006 9 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record006_frame009_indices record006_frame009_graph record006_frame009_links
def record006_frame010_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x21bc2081d031ffbfa7eefc9f73e97c8eddcbb9471ee25c3b826f4de5ba36c6d4d11a0b36662cb194322638c6d8b307604bed7d2f55daba9722df5bab51672a050aa093e2794e69c1342674c89692c23245c8790ca1442082d022023fc7c0f61e53c8788ed1d83a0730e59c1378628c39812fa5e4b91672c2554a714c28a4f89c12e2564708a10f21640c7d8f71ce3886e8da1a8338650bc140238358690c8188298520a013c2704d0961281e83b06e0d4130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record006_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record006_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record006) (record006.maps 10)
      (record006.inverseMaps 10) record006_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record006_frame010_links_0000 (interval_append _ 64 128 154 record006_frame010_links_0064 record006_frame010_links_0128))
theorem record006_frame010_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 10 :=
  of_group record006 10 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record006_frame010_indices record006_frame010_graph record006_frame010_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (Fin.cases (record006_frame008_supported hcells) (Fin.cases (record006_frame009_supported hcells) (Fin.cases (record006_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x36bd9facef65db2998fac6961fad29530a8a52b2905430a044ed262530896f4b425812b49534a5a51527c93749824a5244914486a3fd1ec8ef470a368fa270b37e1b0cd5e6843379910b0857429e94aca2e50527a13809a24be256126891047722a910c8464102000f7c79e3151828b385782a814b0a144e226212788f445621910407983a81b40d086442e01600ab053c29014109d04b024a117082034412a09203901bc0c606002f01740b605a02c81600ae05602a80e806e02b014009804a023011008404001f00f007402c013008804001c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame001_links_0000 (interval_append _ 64 128 143 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a3db64d9f6adb50da28cfc666ae7d5b2ac854629dd4a0a3b509a55d28c90c47d23991a88c14562269110876432214908481f4069fa4fae7c63d29e4ccd65a52ca1560a8651c283937c8464121ec0f187643a01c68de06cc3541a10cc063c30e1758b6456a2a314909c44be21410787e83e61eb0f287783ac1d00e487083761b40d6867c33018a0c085e82d81650b005642a414b0a204d825e121086035412a09203901bc0c606002f01740b605a02c81600ae05602a80e806e02b014009804a023011008404001f00f007402c013008804001c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame002_links_0000 (interval_append _ 64 128 143 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xea9bd3776ced81a9b4c67ec356eada594b0d5b2af5449f13da724de9ad34a664c49812ea5a4ae95128a4b4909091ea3a4688c5039d73a8710de9b0352670bb1752d85a4b29632c0570ad1572a8544a714b28a5089e1372684b89590d21840c800fc1f43dc798f11dc3ac740e51c43706c8d319c32c628c21823005f8be17a2ec5d0b816a2b44888e0e01b43085e0b816c2c8580ae1582a8540a60e81b82b050098128230440841001f03c0740b0130220400700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame003_links_0000 (interval_append _ 64 128 143 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x316d7eebe85d8ae816fab6c5a7aafd4b4a4d50928093c49d24daa4fd25e8ec46da31916a8a4447a2150ea85d42320c90407fe3f61f48f7c7a93be9dacd826533239838bfe5e12e916d8a9253b28113d09cc4d726492ec9644a524992048e246422490f084c4172038f9c7b63611a80c5460c2f61740b645922bf1588a74514278136894848e23111108443e41e50eb071836a1a80ce06142f2164098832012a09203901bc0c606002f01740b605a02c81600ae05602a80e806e02b014009804a023011008404001f00f007402c013008804001c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame004_links_0000 (interval_append _ 64 128 143 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5e85b65b05a059a58a5845775335014fb4e94e34d44ce4c248a48647046846045845044844243d43743042942241540e4023fb3f43e73e03a437236d35a35334333c32d2ec2e62c82c22ba2b02a829e29829028927e27627126525e25224723d2302291e71e11c11b91af1a71a119919318b18417916f16815b15614d14213812a12311c1161101091040f80f30e80d80b108a08806f06c06005d05b05a05805705605505405305203a03702b02802602502302202102001f01e01d01601301101000e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame005_links_0000 (interval_append _ 64 128 143 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6ea6c26bd6aa6a16906876786175d65d25bb5b259d59257d53252b5074fd4f24e54d94cb4c34bc4b34aa49f49948847f46e46445944643b3db39a39637e37335d3543412f62ef2c92bd2af2a429a28f28728027726e26225924624023222821d2071fe1c51c11ae1a619d19618e18517f17d17917216b16515514f14013c13812e12712311e11a11410d1000f90ed0e00b309309007106e06205f05d05c05a05905805705605505403a03702b02802602502302202102001f01e01d01601301101000e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame006_links_0000 (interval_append _ 64 128 143 record007_frame006_links_0064 record007_frame006_links_0128))
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x6431388bedeeef75b8db2cb64acd5ea751a6d0a83399bcd26731974b6592a93c92451f8ec6a2f148843e1905823e5eef378bb5c4e16cb5da8d368b399acc6531d88c25faf574b75a2c15ea652a7536984ba5524914823916884320d027e3d9e0e873391c4e06f371b0d66933188be5e2b15492462210c82401f8f87a3c1d8e06e2b140984a2311084401f0f0742c13088401c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame007_links_0000 (interval_append _ 64 128 143 record007_frame007_links_0064 record007_frame007_links_0128))
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad3a90a87a6ca5fa3fa32a0f9a194693e9209138f58e88c684e84581c8097f67e07cf7be7a879b79078076f76073b7277006eb6d96b36a063c5e05d95bf5b15905835645024fa4da4cc4bc4ac49e48f48047546d4604524444254153f53e43d63b63a633832d3052f52e62d92cd2bd2ac2a029628627526724923921a2071f81d91cb1c21ba1ae1a019117316514611c0b408f08c07006d06105e05c05b05905805705605505405303a03702b02802602502302202102001f01e01d01601301101000e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame008_links_0000 (interval_append _ 64 128 143 record007_frame008_links_0064 record007_frame008_links_0128))
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6df6a069b68367765f6526375ec5a65a158b57e56f56154f4f94f24de4d24ca4bf4b14a949e49548f48347846c45944a4304244174053f93b336d36835034a33332b3162c02b92a229c29128527a27026525c25324a23d23521e2111f71e81df1cc1c018f18b17c17717016c16616015d15715414f14914313813212912311d11110e10c10a1051000fb0f00ea0e00cf0a908708406b06805c05905705605405305205105004f04e03a03702b02802602502302202102001f01e01d01601301101000e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame009_links_0000 (interval_append _ 64 128 143 record007_frame009_links_0064 record007_frame009_links_0128))
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0658.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0658.count (({ width := 9, code := 0x6833d9dcbe4f1989c1df6f77aba5c2d366b0556a94fa65228f44a04fe7d3d9dce66d3297cae4f248f46e31168ac3e170480bede0ef7539dc6e26fb6db4d96c359a8d166b298cc25fae56cae56aa14aa15027532984ba59289247a2d1084401f4ee74399c8e270379b4d86a3397cb85b299488e44211047e3e1e8f0763a1c8d86a2a138944822108803e1e0e8702c13088401c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record007_frame010_links_0000 (interval_append _ 64 128 143 record007_frame010_links_0064 record007_frame010_links_0128))
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0658
    Papers.RationalityTen.SharedFrameCatalogue.group0658_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb35b2fb2cb29b24b1dafcaf5af0ae9ae0ad8abcab5ab0aa7a9ea929d59cc9c59bb9af9a598197a97096395894e93e93592c9209139068fc8ef8e28cd89588b88087286385584683a82d81f80c7f97ec7db7ca7b479b79078076f76075073572170c6f966b66465e65864d64061b61560c6015f55e85d95d25c95bf5b15a059558857b56854053952f52451750a4fb4f24e74dd4cf4c04b44a649848747546d46045244443641f40f3fd3ee32d3203133052f52e72a029628627526725a2071f81e71d91c21ba1ae1a019118313512911a10908e08d08c08b05705605505402102001f01e01101000f00e00c00b00a009006005004003000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame001_links_0000 (interval_append _ 64 128 165 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc0cc06c01bfabf0be9bc2bb8bb1ba7b99b91b74b68b64b55b44b38a78a6ca65a5ea4ca42a23a17a10a079f49e89d79c89c19b59a399498e97796895a92091390b8fe8e98d98c68b48a989b8898798708598458318108007f77ea7d47c07a679077b7676c46b66ac6a569868e67066365a65264563b62b61d61360b5fe5f35eb5db5cf5c359158357957156255554353352851f5115044fb4e84da4cc4b34a449b49048247746245344443636b35834d34133131f2c72b72ad2a12932862322232132011e21d51cd1c41b51a815514313312309409309209105905805705602102001f01e01101000f00e00c00b00a009006005004003000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame002_links_0000 (interval_append _ 64 128 165 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x3c5f0fc1effbdeefb9edbb3ec3adeaba5e8b9fe7399e5b6ad9b62d7b5ad5b50d374ad1f44d073dceb37cd331cbb2cc9f22c7715c470dc2704bfef9bd6f1bb6e8b8edfb5acdb12baadab2ab6a9a969ea5e90a2e6698e609765a95e509364a91e449063d8ea378d2318ba2c89a2086a148460e82e0780dfe7edf87d5f17b5ea781d6731c4705be6e5b56c5aa68d9c65957551515394a519244851e46916448f53c0eb3a0df36cd734ccf32ca7280992506418c62184411003f0f8210801f078110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame003_links_0000 (interval_append _ 64 128 165 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd2568eb455a1ed07680b34d98ecbe65a32ad944c74632b159896c3c61bad5568ab385962c7d62aae956bab2557cab05542a6d516a7f53a29a14c0a5b52228b14329db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c28c2458227911a87b438a16108482d40c1d80ea474739e1cc4e4e6f73729b68d966c035a1a9cd3268833e19accc265d32618dcc4c5f02f01750b925bd2d996a4b3458d2bf15c4acc5622a794f4a5e51928413e49d44db26912f495449c2470eb473638c1bd8db06c430617a0b8c5a62c215c096448e23411107f43dc1e00e8870c3721640a78500260094049824812205902c015c0ac021010007c03c011008003c01c00c00580280120060028010006000 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame004_links_0000 (interval_append _ 64 128 165 record008_frame004_links_0064 record008_frame004_links_0128))
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x50aa1141a82d04a053fe7e4f89ed3d2784ec9d53a6744e69cb2d657caa94f28e4f49692322e43c818f71da37c6b8cf17e2dc5889f11a1fc3685f0aa13c2183705a06405802fddf7bec7c2f55e53be76eec1d6ba673ee61c8b8a706d21a0b3c672cd19732463ec698bb1261ac25822ff5f6bd5782ed5cab756aacb58cb015e2b6560ab55329f538a5947a8b5029dd372644c29652b25349891d2123d470784eb9d1398708dd99f330648c7186300544a413e26a4b49412123a45c880e41b233c610760ea1d03984b0941242402104007c0f01102003c0700c0160280480600a01001800 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame005_links_0000 (interval_append _ 64 128 165 record008_frame005_links_0064 record008_frame005_links_0128))
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x38ae2386e1382e037edef78dd772dbf69d9761d7759d5726c871cc6313c3f09c1701bfafabdef3bc2edbaae7b92e2b6ed7b4ecbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe789da739c66e9ae5f962509222c8a2248861d86a148420c82605809ff7f5fb7e5f77d5f37b1e7789da759d273dcb721c570dc16fdbd6edb96b9a86899b6659765593645825ed745b5384d1304b5294990640d003f8fb3e4d8350d0330c5304bd2e8b62cc8f220831f859160571583a0e4380dc1e0741c06c110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame006_links_0000 (interval_append _ 64 128 165 record008_frame006_links_0064 record008_frame006_links_0128))
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe9774239d1cc8e52720b75db88db46d23649b02d566a7b521a82d3a699b0fd850c115feafa57aab825b7ad71698b3c5942c49600aee56dab1d566aa854aaa0d4e0a16501a7c13c09d04de26993289824b7a56d28e93c494a45d2088ee473a3811b28d2465a3051748b34561f78f907b63d19e48f0072d38e1c34dfa6ed36e9b1cd6e6a634a1a10cea66a32b990cc605d82e396e0b505982c415c8ac455129f94bca4051528113b89b64c726012e49644ac252926c92848d2430dfc6d43571a08cb06322b91548a6451427a135886c4181fe0f8075838c1b60d3865c310138094846c21a094049824812205902c015c0ac021010007c03c011008003c01c00c00580280120060028010006000 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame007_links_0000 (interval_append _ 64 128 165 record008_frame007_links_0064 record008_frame007_links_0128))
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82781e81580f80a8067e27da7d57d17c87c17ac7a57a079a79579072471c71270a7006fa6da6ce6c46bc6b36ab6a169768b68167867266f65e65064461f61460b6035f95f05e65dd5d45cc5c05b75b45a359558a57b57456d56655f55955154a54353c4d84cd4c54b84b04a748147346a45f45845044643a43042441941040d3fc3eb3e03b43a73a039738e38337936f36435934f34334032f31e3133062ff2f82f12ea2e42dc2d52ce2c723c23222421a20c2041cb1c31bc1b51ae1a817a16e16715e14b14313c13512e1280fa0ee0e50e009209109008f05905805705602102001f01e01101000f00e00c00b00a009006005004003000 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame008_links_0000 (interval_append _ 64 128 165 record008_frame008_links_0064 record008_frame008_links_0128))
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xffe7f4bf65f8cfb07ce3bf5dd0ed175fbaa9d2ce2870937e9bc8dcb6da30357f2be25e72ee1746b455982c69610af5570ab21568aa054629dd4c4a57522a8c14369bc4d4265d3089714afa52526a921487a3f51d48de46622e114888843b21910a4842418206100c7f43f11b64d8a6ae34d1a10cde6112fe1798ba85c12d69650b0056c2ac150ca5c52328893f09ce48823a118c8a043d21590548023ed1ed8f2476c3aa1cc0e106e03541a10cc063c30e17e0b905a42c0157083c4102010fd07cc3d81c90e106ec3681ad0d306042f41730b605802b21520a5851027a1180888428206094049824812205902c015c0ac021010007c03c011008003c01c00c00580280120060028010006000 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame009_links_0000 (interval_append _ 64 128 165 record008_frame009_links_0064 record008_frame009_links_0128))
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8df8d88d38cb8c58bf8a489d89889088a88486585e85885284c8457c87b87b07a779d79776275474873e73472871a7117076fa6f06e66dd6cf6c36b567366365564b63f63262261960e6005f45e85de5ce5bf5ad59758e58657e57656e56355b55254a4e54d54cd4c44ba4b447946945b45144543842841f4144063fa3ee3e43d43c53b337436635a35034633a32c32331930c3022f82ef2e12d52c72b42ab2a329b29328b28027826f2671fa1f31ec1e61df1d81b71b01a81a119919016716015915114513e13612f12711e0f50ee0e70df09409309209105905805705602102001f01e01101000f00e00c00b00a009006005004003000 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame010_links_0000 (interval_append _ 64 128 165 record008_frame010_links_0064 record008_frame010_links_0128))
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
def record008_frame011_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1073.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1073.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1073.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1073.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1073.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1073.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1073.localPairCheck (smallEmbedding record008) (record008.maps 11)
      (record008.inverseMaps 11) record008_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame011_links_0000 (interval_append _ 64 128 165 record008_frame011_links_0064 record008_frame011_links_0128))
theorem record008_frame011_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 11 :=
  of_group record008 11 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1073
    Papers.RationalityTen.SharedFrameCatalogue.group1073_facts record008_frame011_indices record008_frame011_graph record008_frame011_links
def record008_frame012_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0740.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0740.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0740.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0740.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0740.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0740.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0740.localPairCheck (smallEmbedding record008) (record008.maps 12)
      (record008.inverseMaps 12) record008_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame012_links_0000 (interval_append _ 64 128 165 record008_frame012_links_0064 record008_frame012_links_0128))
theorem record008_frame012_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 12 :=
  of_group record008 12 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0740
    Papers.RationalityTen.SharedFrameCatalogue.group0740_facts record008_frame012_indices record008_frame012_graph record008_frame012_links
def record008_frame013_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1071.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1071.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1071.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1071.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1071.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1071.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1071.localPairCheck (smallEmbedding record008) (record008.maps 13)
      (record008.inverseMaps 13) record008_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame013_links_0000 (interval_append _ 64 128 165 record008_frame013_links_0064 record008_frame013_links_0128))
theorem record008_frame013_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 13 :=
  of_group record008 13 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1071
    Papers.RationalityTen.SharedFrameCatalogue.group1071_facts record008_frame013_indices record008_frame013_graph record008_frame013_links
def record008_frame014_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1072.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1072.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1072.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1072.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1072.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1072.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1072.localPairCheck (smallEmbedding record008) (record008.maps 14)
      (record008.inverseMaps 14) record008_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame014_links_0000 (interval_append _ 64 128 165 record008_frame014_links_0064 record008_frame014_links_0128))
theorem record008_frame014_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 14 :=
  of_group record008 14 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1072
    Papers.RationalityTen.SharedFrameCatalogue.group1072_facts record008_frame014_indices record008_frame014_graph record008_frame014_links
def record008_frame015_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1070.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1070.count (({ width := 8, code := 0xa4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1070.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1070.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1070.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1070.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 128 165 :=
  interval_of_check _ 128 37 (by decide +kernel)
theorem record008_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1070.localPairCheck (smallEmbedding record008) (record008.maps 15)
      (record008.inverseMaps 15) record008_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 165 record008_frame015_links_0000 (interval_append _ 64 128 165 record008_frame015_links_0064 record008_frame015_links_0128))
theorem record008_frame015_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 15 :=
  of_group record008 15 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1070
    Papers.RationalityTen.SharedFrameCatalogue.group1070_facts record008_frame015_indices record008_frame015_graph record008_frame015_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (Fin.cases (record008_frame011_supported hcells) (Fin.cases (record008_frame012_supported hcells) (Fin.cases (record008_frame013_supported hcells) (Fin.cases (record008_frame014_supported hcells) (Fin.cases (record008_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc0cc06c01bfabf0be9bbfbb5bb0ba5b98b90b78b6cb66b5bb49b3db31b27b20b14b06afaaf5adfad0ac1a78a6ca65a5ea4ca42a23a17a10a079f49e89d79c89c19b59a399498e97796895a8c38b18a88988868768108007f77ea7d47c07567407297126aa69568b6586406366135fe5f35ea5d05c45b457856055352750e5014f84dd4cf4c049b48247746f45544643943041b40d3fc3f23a538b37e34d33131f3122f62e62d42ad29328627b2612512422392232132011f41cd1b51a81510fe0bf05e05d05c05b05905805705604204104003803703602502402302001f01e01000f00e00b00a009005004003001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record009_frame001_links_0000 (interval_append _ 64 128 160 record009_frame001_links_0064 record009_frame001_links_0128))
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x692b475a2ad0f683b4059a2cc665db2cd950ca163d31a98b8c5062130e5854c1d607b00d7eabee5f52f5577eba95aaad15670b2c58fac555d2ad7564aaf9560aa854daa2d4fea7453429814b6a4451628652f896b4aca52126c92c46122c113c88d43da1c500e7f23ee1f18e8472c3929b54d766b234419accc265b31e18a8c325d22dd96c8b1456e2b29580a8253229213e49b64d226612b493c49024491bc8be4502220f8c78e3be1c60db06c435919c8c946262e31610ae056029013e89ac4c024711a08884241e00e186e42c010b06481780ba05c02d81640b005702b010808204001c00dc06c025012008c04001f00f004001e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record009_frame002_links_0000 (interval_append _ 64 128 160 record009_frame002_links_0064 record009_frame002_links_0128))
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xe2b88e1b84e0b80df77addf74dc76edaf67d8f5fd6f57d4f50d374ad1f44d0738ccf2ec9b21c7318c4f0fc2705c06febeaf7bcef0bb6eab9ee4b8adbb5ed3abaaaa9aa2a7a9a9e2769ce719ba6b9063d8e23388a1b8620a80e007edf77d5f27a1e3779d1729c7701bc6e9b76a9a46799764d916397d5d96f5ad645855e56d495013c4c129499234550f425003ecf93dce9390df36cd4340cc328bd2d8b322c701743f0f83d0f03a0e4380dc330c8310bc2e0b422084200741c06c1003c0e02c0a024050100300400 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record009_frame003_links_0000 (interval_append _ 64 128 160 record009_frame003_links_0064 record009_frame003_links_0128))
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x71fb8e9c6ae2f7143889b60da46cab615ae4d6268bb42d9f8cec66cb325970cb1655329193ac96648b229906c7c5f3af6178cbb45d12e3968ab365922c49600aec56dab5559cac75602ae5568aad5532a7d3549984c325d92c895347ba3951a68c3458a28109684441ea0d8ed47443989b00d346873379984cb4654325190cc7a5c62d01630abe54329a94b4a2850627c134896c4a8250121c8f246b23391808b64562290f0c7303811a78cc063e31417d0ba85b22ae14789f84e625912488e046622a111887042c1e00db868828610606901780ba05c02d81640b005702b010808204001c00dc06c025012008c04001f00f004001e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record009_frame004_links_0000 (interval_append _ 64 128 160 record009_frame004_links_0064 record009_frame004_links_0128))
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x777bb79da0ec3759ba91c14dfb6f63765b8cdb26b33551a82d2c68cb4159decde66632ed94cc90642b1c98bcc475d2ae5970eb745b0ad35602aef56e2b1d568aa054529e54cea56520a8ad440a0d4fca78930897d4bb25bd2d096149f24dd260929491246d1ec8ef47423850127e33e79d38e4470d36b1abcd3268b3339944c785c32ce1624a9e52b28c14349e04dd26692688ee46722e90fc85c41f20b90007de3df1e98d5065a31a1700af055229e14089b84bc22b10407e03dc1d00df86c03501910c005c02c814809d04cc21c0ed06881780ba05c02d81640b005702b010808204001c00dc06c025012008c04001f00f004001e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record009_frame005_links_0000 (interval_append _ 64 128 160 record009_frame005_links_0064 record009_frame005_links_0128))
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xbfd7f6fd5f6be17b6e6dc6b836ead9dadb3d662c958bb0b5febbd73adb5a2b2560ab9556a7d49a5b49e90d1aa2943a7bcf09d73926ecd79a1332634c197b2e65acae95128a31c5c8a913a2444283d05e07c09806ff5edbd77a6f3dd3399726dd1b3b616a8d29a2b4066ecc194af85d0b8164abe576add52a9f532a093aa704d6961282474848e51a22f4547e0f41e03906ecdb1b133c658c69762d65a0b2152298518a11392684bc951152124086f0c014c1542a0530a41402784e09a1042003f0700dc1b02504808c1001f03c0400780e0160280480500800c00800 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record009_frame006_links_0000 (interval_append _ 64 128 160 record009_frame006_links_0064 record009_frame006_links_0128))
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x89288a88688087b87584283a83683082b8258088037fc7f77f07ea7e27dd7d67d17ca7c47bd7b97b57b176975b74e7146f96e26d26c36ae6a36a169568e65c64d6386206055ee5e55e35d75d05c75bb5ad5a55a159759058958557b5745705024f54ee4a548e48246745344643c4304294223e43d03c339d38637a37336736035934833d33733232832131b31730d3063002fc28222a22021a1c61b81b119a19118517c17613012711e1121090ff0f80e00da0d50c60c207b07907807106f06e05e05c05b05905705604204104003803703602502402302001f01e01301200f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame001_links_0000 (interval_append _ 64 128 158 record010_frame001_links_0064 record010_frame001_links_0128))
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1066.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1066.count (({ width := 8, code := 0xf5f4f3f1f0efeeedeceae9e8e7e6e5e3e2e1e0dfdedcdbdad9d8d7d6d1cfcdcac8c6c5c3c1c0bfbcbbb8b6b4b3b1afaeadaaa9a8a6a4a3a29f9e9d9c99989792908f8c8a89878685848281807c7b7a79777675737271706e6d6c6a696867656463625c5756554e4d4c49474544433e3d3b393837363332312e2d282625242221201e1d1c1a191817161514131211100f0e0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1066.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1066.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1066.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1066.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1066.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame002_links_0000 (interval_append _ 64 128 158 record010_frame002_links_0064 record010_frame002_links_0128))
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1066
    Papers.RationalityTen.SharedFrameCatalogue.group1066_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1057.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1057.count (({ width := 8, code := 0xf5f4f3f1f0efeeedeceae9e8e7e6e5e3e2e1e0dfdedcdbdad9d8d7d6d1cfcdcac8c6c5c3c1c0bfbcbbb8b6b4b3b1afaeadaaa9a8a6a4a3a29f9e9d9c99989792908f8c8a89878685848281807c7b7a79777675737271706e6d6c6a696867656463625c5756554e4d4c49474544433e3d3b393837363332312e2d282625242221201e1d1c1a191817161514131211100f0e0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1057.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1057.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1057.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1057.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1057.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame003_links_0000 (interval_append _ 64 128 158 record010_frame003_links_0064 record010_frame003_links_0128))
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1057
    Papers.RationalityTen.SharedFrameCatalogue.group1057_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x298529a4d48e9151ea1340e80cfe9f73de71cdc9ab34a66cc89832ee5b4b395929a50c9d93324a32c5c8a90e61742983d05205c017fefddf83d6798f0ddb3af74ce79ce39171ae19be3726d8da1b03596a6d3da3b4067abe577aeb586ae95caa6536a5547a845009e9292464848bd1322243e85106a0a3f87c4f61e93c0768ea1d1390708de1b92fa56caa15125649490918222428821011c83846d0d219c320620ba1682c4538a40e21bc370680ce1982c8580ae154298520800fc1f03706c0d4128240460800f81e0260480780e01a0280480800800c00800 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame004_links_0000 (interval_append _ 64 128 158 record010_frame004_links_0064 record010_frame004_links_0128))
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0968.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0968.count (({ width := 8, code := 0x9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0968.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0968.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0968.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0968.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0968.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame005_links_0000 (interval_append _ 64 128 158 record010_frame005_links_0064 record010_frame005_links_0128))
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0968
    Papers.RationalityTen.SharedFrameCatalogue.group0968_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x73372e72b72572071c7006fa6f76f26ea6e26d06c86c16b86af6a569b69368d68367766c66565864c63d6055f85ea5c95b95a859c58b5795675655525475255124fe4ec4de4cb4bb4b84a649a48f47846545545043842c42441d40e4053fd3c73ba3b138a37a36f35c34a34033732331930e2e42d02c52ac29c29228c27626d26124a23522c22420d1ff1f31ee1df1d51cc1c419117116916313d13512f12612011611110e0f60f10eb0e30de0d70d10c40bd0b70ab0a907307107006a06806705705505405205004f04104003f03803703602502402302001f01e01301200f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame006_links_0000 (interval_append _ 64 128 158 record010_frame006_links_0064 record010_frame006_links_0128))
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x24e49a93325e4ac9290d20e40c7e8ef1ce33c658c71822d4548a112a23c448810f21cc3485f0a6074077f4f95edbcd786ef5dabae75ae9dd1b8f70add9b6b646aed31a5b3e66ccb591315616c297caf15dabad722e05bcb0158aac52ca35422784e49b134a614bc9692123545a86d07a094087d4f69e53b6744e49c43706c0d41a633e66ccb9952ce52ca113b232440850fe1f23d4798f11b034c660c217a2e45a0a91482804a0920d61a8348630c21802905009e1342584a0780ec1d03606a0d0128240460800f81e0260480780e01a0280480800800c00800 } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame007_links_0000 (interval_append _ 64 128 158 record010_frame007_links_0064 record010_frame007_links_0128))
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
def record010_frame008_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0615.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0615.count (({ width := 8, code := 0x9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0615.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0615.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0615.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0615.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0615.localPairCheck (smallEmbedding record010) (record010.maps 8)
      (record010.inverseMaps 8) record010_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame008_links_0000 (interval_append _ 64 128 158 record010_frame008_links_0064 record010_frame008_links_0128))
theorem record010_frame008_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 8 :=
  of_group record010 8 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0615
    Papers.RationalityTen.SharedFrameCatalogue.group0615_facts record010_frame008_indices record010_frame008_graph record010_frame008_links
def record010_frame009_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0612.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0612.count (({ width := 9, code := 0x30380bf5f6f97bbc5deed75b9dcadf6eb6daed568b3d9acb64b1d82bf5eae56aa951a6d228b43a0cfe7d399c4d6672f974b24f259147e3d1c8cc62290e86c32130782c1204ff7e3c9dceb73b91c4e06fb75b4d86ab4da0ce66b218cc3613017cbb5cad964b1572b154a852a91429e4922d10873e9e4ec73389b8d86a32188c05d2d960aa51281389247200fc7c3d1e0ec6a34198c45e2e148a04e251208c381b0d0602e160803c1a0c0582410070200c0200 } : Fields).get c.val)
theorem record010_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record010) (record010.maps 9)
      (record010.inverseMaps 9) record010_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame009_links_0000 (interval_append _ 64 128 158 record010_frame009_links_0064 record010_frame009_links_0128))
theorem record010_frame009_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 9 :=
  of_group record010 9 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0612
    Papers.RationalityTen.SharedFrameCatalogue.group0612_facts record010_frame009_indices record010_frame009_graph record010_frame009_links
def record010_frame010_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0610.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0610.count (({ width := 8, code := 0x9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0610.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0610.localPairCheck (smallEmbedding record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0610.localPairCheck (smallEmbedding record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0610.localPairCheck (smallEmbedding record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0610.localPairCheck (smallEmbedding record010) (record010.maps 10)
      (record010.inverseMaps 10) record010_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame010_links_0000 (interval_append _ 64 128 158 record010_frame010_links_0064 record010_frame010_links_0128))
theorem record010_frame010_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 10 :=
  of_group record010 10 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0610
    Papers.RationalityTen.SharedFrameCatalogue.group0610_facts record010_frame010_indices record010_frame010_graph record010_frame010_links
def record010_frame011_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0607.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0607.count (({ width := 8, code := 0x9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0607.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0607.localPairCheck (smallEmbedding record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0607.localPairCheck (smallEmbedding record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0607.localPairCheck (smallEmbedding record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 128 158 :=
  interval_of_check _ 128 30 (by decide +kernel)
theorem record010_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0607.localPairCheck (smallEmbedding record010) (record010.maps 11)
      (record010.inverseMaps 11) record010_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 158 record010_frame011_links_0000 (interval_append _ 64 128 158 record010_frame011_links_0064 record010_frame011_links_0128))
theorem record010_frame011_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 11 :=
  of_group record010 11 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0607
    Papers.RationalityTen.SharedFrameCatalogue.group0607_facts record010_frame011_indices record010_frame011_graph record010_frame011_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (Fin.cases (record010_frame008_supported hcells) (Fin.cases (record010_frame009_supported hcells) (Fin.cases (record010_frame010_supported hcells) (Fin.cases (record010_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xafcaf5af0ae9ae0ad8abdab6ab1aa9aa0a959d59cc9c59bb9af9a593e93592c92091390689588b88087286385584683a82d81f80c7f97ec7db7ca7b479b79078076f76075066966165b65364863a61a61360a5ff5f35e55d95d25c95bf5b15a053e53452a51f5125044fb4f24e74dd4cf4c04a749948b47b47546d4604524444364234134023f337a37036335534833d32d3203133052f52e72d52c92ba2a82a029628627526725a2071f81e71d91c21ba1ae1a019118316f16115214213512911a1090ff05705605505404304204104002a02902802702102001f01e01101000f00e00c00b00a009006005004003000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame001_links_0000 (interval_append _ 64 128 160 record011_frame001_links_0064 record011_frame001_links_0128))
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbc2bb8bb1ba7b99b91b77b6bb65b58b47b3ba78a6ca65a5ea4ca429d79c89c19b59a399492091390b8fe8e98d98c68b48a989b8898798708598458318108007f77ea7d47c06bf6b16aa6a069568b66e66165964f64363962b61d61360b5fe5f358c57e57756b55d55054353352851f5115044ec4dc4ce4bf4b34a449b49048247746745744843b3c03b13a539a38b37e36b35834d34133131f3082f62e62d42c72b72ad2a12932862322232132011e21d51cd1c41b51a819418317416715514313312311605905805705604304204104002a02902802702102001f01e01101000f00e00c00b00a009006005004003000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame002_links_0000 (interval_append _ 64 128 160 record011_frame002_links_0064 record011_frame002_links_0128))
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xee7b6ecfb0eb7aae9ba3e839de6b97dab66d8b5ed6b56cf73acdf34cc72ec5711c3709c12ffbe6f5bc6edba2e3b7ed6b36c4aeab6acaadaa6a59926197a5b9625593e4c9264690e408f63a8de348c62e84a0f83208812007f9fb7e1f57c5ed785d7735c7711c16f9b96d5b16ada4675985c96e5a9665855c55d545454e529464f9364b928491214791a459123d4f03ace837cdb35cd333ccb310bc2d0ae29ca026494240411003f0f83a0e4380dc2a0a42809c210801f078110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame003_links_0000 (interval_append _ 64 128 160 record011_frame003_links_0064 record011_frame003_links_0128))
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x669b31d97ccb4655b2898eec6862cb13987ec385aaad15670b2c58fac55536a8b53fa9d14d0a604eda71d3709aa4cda6412fe96e4ae252d27292d493a4391ee8e146122c113c88d43da1c4eb674d3a11cdce5872537a1b8cdb06c935f1accd4e69934419f0cd66612f5176cb9e5c42dc16c4b5259a2c695f8ae25662a99500a6252328c94209f24ea26d93489844af25012488083f21f18f5878e3be1d68e6c71837b1b60d8869c3391928c4c60c2f41718b4c5842b812c891c4682220fe87b83c01d10e186e434e1940c185cc2c814f0a004c024605902c015c0ac043021010408002a01480a004e021010007c03c011008003c01c00c00580280120060028010006000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame004_links_0000 (interval_append _ 64 128 160 record011_frame004_links_0064 record011_frame004_links_0128))
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xdfb7bde375dcb6fdab66d8b5ed6b56c9b21c7318c4f0fbcef0bb6eab9ee4b2ec6b06bdae2b4abeaba9ea3a7e9ba628da1a7f9e2769ce719ba6b8a62588a1e86e1884e0f82e08812017fdfd7edf97ddf575dd3741cc725c6715c3705bf6f5bb6c1a968d9d66d9965d9564d916197e5dd7054d4e525455013c4e1344c12d4a52646d1543d0941903400fe3ecf9360d4340cc314c12f4ba2d8b32a8a32749723c8820c7e1ec3a0e4380dc340cc320c427098250901e0741c06c110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame005_links_0000 (interval_append _ 64 128 160 record011_frame005_links_0064 record011_frame005_links_0128))
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x91e449063e8ee388d2328c22e8b22a81a03801fd7e9f77a1e5789df771d972dc8715c26fdbc6e1b56c9af6b1a969da267598649906398c629885c16e5b16a5a166591625815e5715a56557555535454f4fd3c4e5364cd304bd2d4ad2949d254851e46d1845914449104390c42104400fc3bceb39ce337cdb35cd4344ce32cc8310bf2e8b52c8b02b8ac2a8a8258932408d22086210822007e1e8751c06b1a0651885f174330c8310c02d0b02b0a82408c220841b06819060110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame006_links_0000 (interval_append _ 64 128 160 record011_frame006_links_0064 record011_frame006_links_0128))
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x9e6769ce709b66a99a649865f972598fa3a8da328ba2a852128420d82e087f9fb7e1f57c9ef7ade8795e277ddc769d5745cd721c6711c2701be661956498f6318961d846057e5ed785d9745c9705b96c561555494f5314952146511425013e4e5364cd304b92c4a928499244811a4510e3f0f83d0f03b0e8390e1378db360d5340ca310be2ecb92dcb52ccb12649624c9022c8921c8520c811f0771c86d1a0651885f174350d0330c8300bc2e0b423088210801a0641805c110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame007_links_0000 (interval_append _ 64 128 160 record011_frame007_links_0064 record011_frame007_links_0128))
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0336.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0336.count (({ width := 10, code := 0x7edf87d5f27bdec7a1e6791e2781de721c5709bf6f1b96a9a8699a4689a066d986559263d8c621856097f5f1795dd745c56e5a96859964589605354b52547515435053f4f53b4e5374d9344c9304b92c4811d46917451114410e4310a4210640d013fcfd3ecf93dcf53ccf13b8eb3a0e5364d5344cd324c5304be2ecb82d4b22bcab29ca32809e2709a26096210811f87b1dc751cc711bc6d1a46417c5a15c541444e1302f0b82d0b02a0a42809c220842007c19060170581003c0e0340b02809020060140400c00 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame008_links_0000 (interval_append _ 64 128 160 record011_frame008_links_0064 record011_frame008_links_0128))
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0336
    Papers.RationalityTen.SharedFrameCatalogue.group0336_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0725.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0725.count (({ width := 9, code := 0xbf5f6f97abcddee972b85bad96aac55ead55aa54e994ba4d1e8b429cce26f369acd26732984ba592993c96451f8dc662f1589c45eef67a3cde2ef773b1d4e873391c4e170379badb6733598cb6532590c76331186c15eae96eb4592c15cac552a14ea24f2691a8c45a29128843a190883409fcfc7b3c1d4e873391c4e06f33194c6612e970b65a2c960ac54291409a4c251208c30178b85a2b150a4501f0f07438170b05428110803c1c0c058281206028100600 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0725.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame009_links_0000 (interval_append _ 64 128 160 record011_frame009_links_0064 record011_frame009_links_0128))
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0725
    Papers.RationalityTen.SharedFrameCatalogue.group0725_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0273.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0273.count (({ width := 10, code := 0x812017f9fb7e1f57c5ef7b5eb7a5e7745ce72dc8715c26cdb16bdad6ada9691a16799b661956458e62d88615826017c5e1745bd6d5ad6959d65549505394c5294851944509404f93c4ed394dd354cd314952247d1c46516455134450f4350b41d04404fe3f0fa3e0f63d0f23bcec3a4e6368d6348ce328c6308bf2f0b92d8b32c0ac2a0a42849f2749b26497214821fc7c1e0761d0721c06e1a8651805b160551484f1342f0b82d0b02a0a42809c220842007c19060170581003c0e0340b02809020060140400c00 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame010_links_0000 (interval_append _ 64 128 160 record011_frame010_links_0064 record011_frame010_links_0128))
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0273
    Papers.RationalityTen.SharedFrameCatalogue.group0273_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
def record011_frame011_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0xb4367ecdd94b23636bcd73adf5a2b055aa1942a834ff9f93e2614bc9712c654ca38d719a304588a712e2143d86f0be1542283705e09c0f813009fe3f77e2fadc738a70adfdbdb776c8d75aab50696d119e33565aca191b1c5ccb896ead459ab1d602ba568aa550a9851aa1940a7c4ec9b93325e4ae941242424768d8fa9ef3d2778eb1cd3846f8dc9b035268ccc99231a620c117a2e45a8b195c26a4bc94123234450879092083fc7c0f11d83986f8d81a6334648560aa150298430841042002a0520a01382104007c0f01102003c0700c0160280480600a01001800 } : Fields).get c.val)
theorem record011_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record011) (record011.maps 11)
      (record011.inverseMaps 11) record011_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame011_links_0000 (interval_append _ 64 128 160 record011_frame011_links_0064 record011_frame011_links_0128))
theorem record011_frame011_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 11 :=
  of_group record011 11 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record011_frame011_indices record011_frame011_graph record011_frame011_links
def record011_frame012_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x7dcfa9f4be67c8f85ea3d37a0f31e5bc872ee4dc8b8f71ce29b8b706dedb1b4b6566ecc195323640c718bb1161cc2d82afc5f2bd5792ed5ceb856e2d65a2b3145287508a093fa7c4e09b935a684ce995312604be9752d25745e8b114a244408790d215424839042023f47d0f81eb3ce784ee1d63a072ce29c03786d4c197e2f05c8b796b2cc588af15c2b2554a71482844fc9d93525e4a49211f2043f47b8f31d23906f0d81a4330630bf1762d8588aa14a2884f84d09812c2503f07c0f41e02a0520a01382104007c0f01102003c0700c0160280480600a01001800 } : Fields).get c.val)
theorem record011_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record011) (record011.maps 12)
      (record011.inverseMaps 12) record011_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame012_links_0000 (interval_append _ 64 128 160 record011_frame012_links_0064 record011_frame012_links_0128))
theorem record011_frame012_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 12 :=
  of_group record011 12 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record011_frame012_indices record011_frame012_graph record011_frame012_links
def record011_frame013_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0742.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0742.count (({ width := 8, code := 0x9f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0742.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0742.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0742.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0742.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0742.localPairCheck (smallEmbedding record011) (record011.maps 13)
      (record011.inverseMaps 13) record011_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame013_links_0000 (interval_append _ 64 128 160 record011_frame013_links_0064 record011_frame013_links_0128))
theorem record011_frame013_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 13 :=
  of_group record011 13 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0742
    Papers.RationalityTen.SharedFrameCatalogue.group0742_facts record011_frame013_indices record011_frame013_graph record011_frame013_links
def record011_frame014_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0189.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0189.count (({ width := 8, code := 0x9f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0189.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0189.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0189.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0189.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record011_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0189.localPairCheck (smallEmbedding record011) (record011.maps 14)
      (record011.inverseMaps 14) record011_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record011_frame014_links_0000 (interval_append _ 64 128 160 record011_frame014_links_0064 record011_frame014_links_0128))
theorem record011_frame014_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 14 :=
  of_group record011 14 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0189
    Papers.RationalityTen.SharedFrameCatalogue.group0189_facts record011_frame014_indices record011_frame014_graph record011_frame014_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (Fin.cases (record011_frame011_supported hcells) (Fin.cases (record011_frame012_supported hcells) (Fin.cases (record011_frame013_supported hcells) (Fin.cases (record011_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x9d39c99c29b79ab99f98097796d96195694b93e93592c92091390689488987e86f86085284683a82d81f80c7f979b79078076f76075066966165b65364863a61a61360a5ff5f35e55d95d25c95bf5b15a053f53752d5225155074fb4f24e74dd4cf4c047546d46045244443637936d36035234533a32d3203133052f52e72a029628627526725a2472372262182071f81e71d91c21ba1ae1a019118317116315414413512911a10907907807707605705605505404304204104002102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame001_links_0000 (interval_append _ 64 128 146 record012_frame001_links_0064 record012_frame001_links_0128))
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa73a67a63a58a48a3ea21a15a0fa049f29e69d79c89c19b59a399491e91190a8fb8e78d78c68b48a989b8898798108007f77ea7d47c06bf6b16aa6a069568b66e66165964f64363962b61d61360b5fe5f358f58157856e56055354353352851f5115044b34a449b4904824773bd3ae3a439738837b36b35834d34133131f2c72b72ad2a12932862732632532442322232132011e21d51cd1c41b51a819618517616915514313312307b07a07907805905805705604304204104002102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame002_links_0000 (interval_append _ 64 128 146 record012_frame002_links_0064 record012_frame002_links_0128))
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xda364d835cd6354d3f4cd2746d0f40cf73acdf34cc72ec5310c3308c0efebe6f5bc6edba2e3aeab6acaadaa6a59926197a5b9625593e4c9264690e408f63a8de348c62e84e108360a81a027f9fb7e1f57c5ed711c16f9b96d5b15c56d5a5655815b55d545454e52946491214791a4591243507404fc3d4f03ace837cdb35cd333ccb314bd2d4af29ca0264941685916057104400fc3e0e8390e0370842007c1e0541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame003_links_0000 (interval_append _ 64 128 146 record012_frame003_links_0064 record012_frame003_links_0128))
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x29d4da652e9549a451e8d45a250e833f9ecee733796cb2572a94ca24d239047635178341205007f3f1d0e773395c8e371385c0df6f375b8da6c359a8d263b198ac461b0982bf5eaed72b755aa54ea551a851a8c45a2912884321104803f1f0e471381bcdc6d359a4ce6532188c05e2d164b0572b154a65127934984a2411872381b8d85c2d160ac52281389832180b858281309044200f07034180b050241006028100600 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame004_links_0000 (interval_append _ 64 128 146 record012_frame004_links_0064 record012_frame004_links_0128))
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x169eb405992c9d632b135732b5558eabc5572a9d536a8b53fa9d14d0a604ec271536a9a84cc263d2fe96e4ae252d27292d46122c113c88d43da1c4eb674d3a11cdce5872537a1b8cdb06c935f1accd4e69934419f0cd66612f69778ba45c72dd96c8b5259a2c695f8ae256628c94209f24ea26d93488023f01f08f5078a3bd1d68e6c71837b1b60d8860c2f41718b4c5842b81530a484fe26d12c891c4682220fe87b83c01d10e186e43521960c205d02c814f0a004c00f607a03c81e00b205802b8158086042020810004202000f807802a0140098048022010007803801a00c00580280120060028010006000 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame005_links_0000 (interval_append _ 64 128 146 record012_frame005_links_0064 record012_frame005_links_0128))
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x259cad95329a50c9c92b23e454868ff1ea3b46f8d719e2fc5b86b0ba14c2684106a0b40c80b005fbbef77ceddd83ad74ce7da333e674cdd98b2c646c798cb16622c3184b045febed7aaf0594b155fabb56aabd56aa653ea714b28f4c89852ca564a6931041fe3f07ccf51e43c275ce89cc3846eccf998324638c31802f05b8b295c2a25209f13525a4a09091d22e440841001f03bc720d919e308348680ce1982584a0921201f83e07a0f01082003e0780a8140260480881001e0380680c0160280480600a01001800 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame006_links_0000 (interval_append _ 64 128 146 record012_frame006_links_0064 record012_frame006_links_0128))
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xc8f1ec6b15c470dc2304c02fdbe6f6bcef0bb6eab9ee4b2ac5b02bcadeb3abeaba9ea3a7e9b9e2769ce719ba6b8a62588a1e86e1884e0f82e08812017fdfd7edf97ddf5765d5745ce729c7715c3705bf6f5bb66d9965d9564d915494d521444fd3b4e1344c12d4a52641903400fe3ecf93c4ea394e0360d4340cc314c12f4ba2d8b32aca42789823c8820c7e1404f1384d0e8390e0370d0330c8310781d0701b0541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame007_links_0000 (interval_append _ 64 128 146 record012_frame007_links_0064 record012_frame007_links_0128))
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
def record012_frame008_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x816027fdfc7e5f67d5f37c5ef7b5eb7a1e5789df771d9729c7711c16f9bb6e1b56c9af6b1a9649906398c629885c16e5b16a5a166591625815e5715a56557555535454f5013d4e9374d1314bd2d4ad2949d2545914449104390c3b8ea398e2378da35cd4344ce32cc82c8b02b8ac2a8a8294a127499258932408d22086210822007e1ec761c46c1a0651885f1244811c460cc320c4300b42c0ac2a06c1a064180541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record012_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record012) (record012.maps 8)
      (record012.inverseMaps 8) record012_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame008_links_0000 (interval_append _ 64 128 146 record012_frame008_links_0064 record012_frame008_links_0128))
theorem record012_frame008_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 8 :=
  of_group record012 8 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record012_frame008_indices record012_frame008_graph record012_frame008_links
def record012_frame009_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x8f2388d2308b22889a238821d86a17852128420d82e087f5fa7ddf47c5ee7ade8795e277ddc721c6711c2701be661956498f6318961d846057e5ed785d9745c9705b96c5655654d505354a52146511425013e4b92c4a928499243ecf73ccef3ace7390e1378db360d52ecb92dcb52ccb12b4a828c9e2649624c9022c8921c8520c811f4781cc6e1a0651885f1244811c460d4340cc320c02f0b82d06819060170541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record012_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record012) (record012.maps 9)
      (record012.inverseMaps 9) record012_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame009_links_0000 (interval_append _ 64 128 146 record012_frame009_links_0064 record012_frame009_links_0128))
theorem record012_frame009_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 9 :=
  of_group record012 9 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record012_frame009_indices record012_frame009_graph record012_frame009_links
def record012_frame010_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0336.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0336.count (({ width := 10, code := 0x71dc4705be6edb86ddb56cdb16bdad6a9a8699a4689a066997651916398b621856097f5f1795a96859964589605354b52547515435053f4f53b4e5374d9344c9304b92c4851e46d18455124410e4310a421063ecf93dcf53ccf1360d4340cc320c4304be2ecb82d4b22809e2709a2609624c8f22c87210811f87b1dc751cc711bc6d1a8651805b15c541444e1003f0f83d0bc2e0b42c0a8290a0270641805c1605013048110400f0380d0300b02809020060140400c00 } : Fields).get c.val)
theorem record012_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record012) (record012.maps 10) (record012.inverseMaps 10) record012_frame010_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record012) (record012.maps 10)
      (record012.inverseMaps 10) record012_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame010_links_0000 (interval_append _ 64 128 146 record012_frame010_links_0064 record012_frame010_links_0128))
theorem record012_frame010_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 10 :=
  of_group record012 10 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0336
    Papers.RationalityTen.SharedFrameCatalogue.group0336_facts record012_frame010_indices record012_frame010_graph record012_frame010_links
def record012_frame011_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0273.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0273.count (({ width := 10, code := 0x741cd729c7711c1701be6f1ba6e1b66cdb16bdad6ada968da06759a65d946458e62d88615825bd6d5ad6959d65549505394c5294851944509404f93c4ed394dd354cd31499234811d46917455134450f4350b3f0fa3e0f63d0f2364d5344cd324c5308bf2f0b92d8b32849f2749b264972509023088214821fc7c1e0761d0721c06e1ac661845c160551484f1003f0f83d0bc2e0b42c0a8290a0270641805c1605013048110400f0380d0300b02809020060140400c00 } : Fields).get c.val)
theorem record012_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record012) (record012.maps 11) (record012.inverseMaps 11) record012_frame011_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record012) (record012.maps 11)
      (record012.inverseMaps 11) record012_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame011_links_0000 (interval_append _ 64 128 146 record012_frame011_links_0064 record012_frame011_links_0128))
theorem record012_frame011_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 11 :=
  of_group record012 11 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0273
    Papers.RationalityTen.SharedFrameCatalogue.group0273_facts record012_frame011_indices record012_frame011_graph record012_frame011_links
def record012_frame012_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0173.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0173.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0173.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0173.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0173.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0173.localPairCheck (smallEmbedding record012) (record012.maps 12) (record012.inverseMaps 12) record012_frame012_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0173.localPairCheck (smallEmbedding record012) (record012.maps 12)
      (record012.inverseMaps 12) record012_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame012_links_0000 (interval_append _ 64 128 146 record012_frame012_links_0064 record012_frame012_links_0128))
theorem record012_frame012_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 12 :=
  of_group record012 12 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0173
    Papers.RationalityTen.SharedFrameCatalogue.group0173_facts record012_frame012_indices record012_frame012_graph record012_frame012_links
def record012_frame013_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0136.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0136.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0136.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0136.localPairCheck (smallEmbedding record012) (record012.maps 13) (record012.inverseMaps 13) record012_frame013_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0136.localPairCheck (smallEmbedding record012) (record012.maps 13) (record012.inverseMaps 13) record012_frame013_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0136.localPairCheck (smallEmbedding record012) (record012.maps 13) (record012.inverseMaps 13) record012_frame013_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0136.localPairCheck (smallEmbedding record012) (record012.maps 13)
      (record012.inverseMaps 13) record012_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame013_links_0000 (interval_append _ 64 128 146 record012_frame013_links_0064 record012_frame013_links_0128))
theorem record012_frame013_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 13 :=
  of_group record012 13 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0136
    Papers.RationalityTen.SharedFrameCatalogue.group0136_facts record012_frame013_indices record012_frame013_graph record012_frame013_links
def record012_frame014_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1706b7c5baadbd6d0b625822bdd5caad75642add548a97542a9dd4d0a574e827093669a14c7a5f92d695d4a724f1254919472a33916e8a144521d0e6c72f3949c8ce387163609ac8d4469234119c4cc065132098c4c426102cf9644b085752b31564a9453c2979480a2250426f932c9704a5249920877c3ae1cf0e386fc36f1af0d3867c32e18f0c3c5c42ce15c8a8c51a279133096449623c116087c4222020f6876c3901b70d206483021750b505782a014409c84b40f607a03c81e00b205802b8158086042020810004202000f807802a0140098048022010007803801a00c00580280120060028010006000 } : Fields).get c.val)
theorem record012_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 14) (record012.inverseMaps 14) record012_frame014_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 14) (record012.inverseMaps 14) record012_frame014_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 14) (record012.inverseMaps 14) record012_frame014_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 14)
      (record012.inverseMaps 14) record012_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame014_links_0000 (interval_append _ 64 128 146 record012_frame014_links_0064 record012_frame014_links_0128))
theorem record012_frame014_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 14 :=
  of_group record012 14 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record012_frame014_indices record012_frame014_graph record012_frame014_links
def record012_frame015_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x2f25e0bbb762e9dcfb7d6e2da5adb4f686cbd94b1f626c157aa814ee9a52ca454668750ba0b3ee79ce79852de55ca193323dfd3f67e6fc1f5be579cf21e23be76cebdd33a373ce65c8b876a2d35a4344678cd996b2a64ac7d8d3125eebc173adc5a6b312da5549c91d1f23545a89d10a1942281cf41df3a8720de9b4352678cb98c3005e8b81652b0540a293a25e48c8c11020e3f47a0ec1c6364388700de1b82a8540a61482084007e0f81082003e0780a8140260480881001e0380680c0160280480600a01001800 } : Fields).get c.val)
theorem record012_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 15) (record012.inverseMaps 15) record012_frame015_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 15) (record012.inverseMaps 15) record012_frame015_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 15) (record012.inverseMaps 15) record012_frame015_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 15)
      (record012.inverseMaps 15) record012_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame015_links_0000 (interval_append _ 64 128 146 record012_frame015_links_0064 record012_frame015_links_0128))
theorem record012_frame015_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 15 :=
  of_group record012 15 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record012_frame015_indices record012_frame015_graph record012_frame015_links
def record012_frame016_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x2e2dc2b7f6eedb5b2b45672cc592b135fabd575adf5a6b055aa4d47a8cd11a0b3e2794ed9cb376684c893f25e4a48e9011d1f8bee7d6f9df1bdf79cf1de23be768eadd2ba1736e55c5b856a2d29a333f668ca99131e630c4582afd5bcb5568aca57aacd262454828e51722343885908a093fa7d8ea1cb38a6fcd99a833c664c79872fe5dcb99682b2540a514226649c8d9142184107c8f11d8388388700de1b8298520a21402084007e0f81082003e0780a8140260480881001e0380680c0160280480600a01001800 } : Fields).get c.val)
theorem record012_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record012) (record012.maps 16) (record012.inverseMaps 16) record012_frame016_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record012) (record012.maps 16) (record012.inverseMaps 16) record012_frame016_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record012) (record012.maps 16) (record012.inverseMaps 16) record012_frame016_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record012) (record012.maps 16)
      (record012.inverseMaps 16) record012_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame016_links_0000 (interval_append _ 64 128 146 record012_frame016_links_0064 record012_frame016_links_0128))
theorem record012_frame016_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 16 :=
  of_group record012 16 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record012_frame016_indices record012_frame016_graph record012_frame016_links
def record012_frame017_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x63162c62962662361f5fd5f35e95e35e05dc5d35cc5c95c25b85b257456956055755354e54453a53653052751e4ff4f24e64db4cf4c943a43643343042d4294093fc3f23ea3e73e23dc3d13ce3c73bd3b538437a37336b36536135c35234c34734033932531730b2ff2f32ec27826d26425a25324e24623d23622d22421c1fd1ed1dd1d11c11b91ae1a419a18f18717d17216c15814c14213712d12511d11410c1050fd0f40ed0e607307207107005305205105004304204104002102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 17) (record012.inverseMaps 17) record012_frame017_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 17) (record012.inverseMaps 17) record012_frame017_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 17) (record012.inverseMaps 17) record012_frame017_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record012) (record012.maps 17)
      (record012.inverseMaps 17) record012_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame017_links_0000 (interval_append _ 64 128 146 record012_frame017_links_0064 record012_frame017_links_0128))
theorem record012_frame017_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 17 :=
  of_group record012 17 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record012_frame017_indices record012_frame017_graph record012_frame017_links
def record012_frame018_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0743.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0743.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0743.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0743.localPairCheck (smallEmbedding record012) (record012.maps 18) (record012.inverseMaps 18) record012_frame018_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0743.localPairCheck (smallEmbedding record012) (record012.maps 18) (record012.inverseMaps 18) record012_frame018_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0743.localPairCheck (smallEmbedding record012) (record012.maps 18) (record012.inverseMaps 18) record012_frame018_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0743.localPairCheck (smallEmbedding record012) (record012.maps 18)
      (record012.inverseMaps 18) record012_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame018_links_0000 (interval_append _ 64 128 146 record012_frame018_links_0064 record012_frame018_links_0128))
theorem record012_frame018_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 18 :=
  of_group record012 18 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0743
    Papers.RationalityTen.SharedFrameCatalogue.group0743_facts record012_frame018_indices record012_frame018_graph record012_frame018_links
def record012_frame019_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0190.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0190.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0190.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0190.localPairCheck (smallEmbedding record012) (record012.maps 19) (record012.inverseMaps 19) record012_frame019_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0190.localPairCheck (smallEmbedding record012) (record012.maps 19) (record012.inverseMaps 19) record012_frame019_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0190.localPairCheck (smallEmbedding record012) (record012.maps 19) (record012.inverseMaps 19) record012_frame019_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0190.localPairCheck (smallEmbedding record012) (record012.maps 19)
      (record012.inverseMaps 19) record012_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame019_links_0000 (interval_append _ 64 128 146 record012_frame019_links_0064 record012_frame019_links_0128))
theorem record012_frame019_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 19 :=
  of_group record012 19 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0190
    Papers.RationalityTen.SharedFrameCatalogue.group0190_facts record012_frame019_indices record012_frame019_graph record012_frame019_links
def record012_frame020_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0772.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0772.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0772.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0772.localPairCheck (smallEmbedding record012) (record012.maps 20) (record012.inverseMaps 20) record012_frame020_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0772.localPairCheck (smallEmbedding record012) (record012.maps 20) (record012.inverseMaps 20) record012_frame020_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0772.localPairCheck (smallEmbedding record012) (record012.maps 20) (record012.inverseMaps 20) record012_frame020_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0772.localPairCheck (smallEmbedding record012) (record012.maps 20)
      (record012.inverseMaps 20) record012_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame020_links_0000 (interval_append _ 64 128 146 record012_frame020_links_0064 record012_frame020_links_0128))
theorem record012_frame020_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 20 :=
  of_group record012 20 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0772
    Papers.RationalityTen.SharedFrameCatalogue.group0772_facts record012_frame020_indices record012_frame020_graph record012_frame020_links
def record012_frame021_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0394.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0394.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0394.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0394.localPairCheck (smallEmbedding record012) (record012.maps 21) (record012.inverseMaps 21) record012_frame021_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0394.localPairCheck (smallEmbedding record012) (record012.maps 21) (record012.inverseMaps 21) record012_frame021_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0394.localPairCheck (smallEmbedding record012) (record012.maps 21) (record012.inverseMaps 21) record012_frame021_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0394.localPairCheck (smallEmbedding record012) (record012.maps 21)
      (record012.inverseMaps 21) record012_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame021_links_0000 (interval_append _ 64 128 146 record012_frame021_links_0064 record012_frame021_links_0128))
theorem record012_frame021_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 21 :=
  of_group record012 21 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0394
    Papers.RationalityTen.SharedFrameCatalogue.group0394_facts record012_frame021_indices record012_frame021_graph record012_frame021_links
def record012_frame022_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1874c22605afdd7c6bcf5bfadb16b2b4959cac95624b005772b6d58eab3509a8013da9dd4e6a6e534c9944c125bd2b6947477239d1c08d9469232cfb07c33d81e74f1877a3951c64e146fa3751b68d8e6b73531a50d086752ea9710b6a5a52ca9614ae45622a894fca5e52026393009724b225612948063ea1e98ef07503931bf8da86ae3411960c645722a914c8a284f426b12c892847422b10d88303fc1f00eb071836c1a70cb86202ec1670ab852027012908d84340f607a03c81e00b205802b8158086042020810004202000f807802a0140098048022010007803801a00c00580280120060028010006000 } : Fields).get c.val)
theorem record012_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 22) (record012.inverseMaps 22) record012_frame022_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 22) (record012.inverseMaps 22) record012_frame022_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 22) (record012.inverseMaps 22) record012_frame022_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 22)
      (record012.inverseMaps 22) record012_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame022_links_0000 (interval_append _ 64 128 146 record012_frame022_links_0064 record012_frame022_links_0128))
theorem record012_frame022_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 22 :=
  of_group record012 22 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record012_frame022_indices record012_frame022_graph record012_frame022_links
def record012_frame023_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x6d26c96c56be6b66ad69768e68868267867066765b65564a63f6375ee5e55dd5d75cd5c65bd5b45aa59f59658e55254b54554053b5364c34b94b54ad4a84a148447a47546d46245945044143a43142441b3cc3c53bc3b43a93a239638d38137836c36532932231c31731130c2aa29d29428627b27026525925124923d2321f21e91e21d81d01c71bb1b21a719d18f18617c17315e15514e14413b13512711d1151090fb0f10ea0df07907807707605705605505404104003f03e02102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record012) (record012.maps 23) (record012.inverseMaps 23) record012_frame023_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record012) (record012.maps 23) (record012.inverseMaps 23) record012_frame023_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record012) (record012.maps 23) (record012.inverseMaps 23) record012_frame023_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record012) (record012.maps 23)
      (record012.inverseMaps 23) record012_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame023_links_0000 (interval_append _ 64 128 146 record012_frame023_links_0064 record012_frame023_links_0128))
theorem record012_frame023_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 23 :=
  of_group record012 23 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record012_frame023_indices record012_frame023_graph record012_frame023_links
def record012_frame024_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0377.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0377.count (({ width := 9, code := 0x33f9ecee73379acce5f2b93c8e3f198ac461b0982badcee36fb6daed166b258ac15ea853a994aa451a6531984be5d2d95ca64f2591c863f1c8cc5a27107f3f1f4f87b3d1e4ef763a5cce368b3d9acb64b1d58aa5429948a250279389a4c25914894421d0c8541a00fa7a3b9d0e26f351a4d06733194c6602e968ae542893c7e3e1e8f06230178b8562a148a0361a0c8602a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record012_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record012) (record012.maps 24) (record012.inverseMaps 24) record012_frame024_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record012) (record012.maps 24) (record012.inverseMaps 24) record012_frame024_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record012) (record012.maps 24) (record012.inverseMaps 24) record012_frame024_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0377.localPairCheck (smallEmbedding record012) (record012.maps 24)
      (record012.inverseMaps 24) record012_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame024_links_0000 (interval_append _ 64 128 146 record012_frame024_links_0064 record012_frame024_links_0128))
theorem record012_frame024_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 24 :=
  of_group record012 24 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0377
    Papers.RationalityTen.SharedFrameCatalogue.group0377_facts record012_frame024_indices record012_frame024_graph record012_frame024_links
def record012_frame025_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0448.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0448.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0448.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0448.localPairCheck (smallEmbedding record012) (record012.maps 25) (record012.inverseMaps 25) record012_frame025_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0448.localPairCheck (smallEmbedding record012) (record012.maps 25) (record012.inverseMaps 25) record012_frame025_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0448.localPairCheck (smallEmbedding record012) (record012.maps 25) (record012.inverseMaps 25) record012_frame025_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0448.localPairCheck (smallEmbedding record012) (record012.maps 25)
      (record012.inverseMaps 25) record012_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame025_links_0000 (interval_append _ 64 128 146 record012_frame025_links_0064 record012_frame025_links_0128))
theorem record012_frame025_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 25 :=
  of_group record012 25 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0448
    Papers.RationalityTen.SharedFrameCatalogue.group0448_facts record012_frame025_indices record012_frame025_graph record012_frame025_links
def record012_frame026_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x72171870f7066fd6f86d76cc6c26ba6b16aa6a169768b68167867261c6126096015f75ef5e65dd5d45cc5c05b757b57456d56655f5594d44ca4c04b54ab4a547e47146845d45644f44643a4304244194103b13a539e39538c38237936f36435934f3433062ff2f82f12ea2e427d27226525b24e24723c23222421a20c2041cb1c31bc1b51ae1a819f19518d18417a16e16715e14b14313c13512e12811f11510b1050fa0ee0e50e007b07a07907805905805705604304204104002102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 26) (record012.inverseMaps 26) record012_frame026_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 26) (record012.inverseMaps 26) record012_frame026_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 26) (record012.inverseMaps 26) record012_frame026_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 26)
      (record012.inverseMaps 26) record012_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame026_links_0000 (interval_append _ 64 128 146 record012_frame026_links_0064 record012_frame026_links_0128))
theorem record012_frame026_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 26 :=
  of_group record012 26 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record012_frame026_indices record012_frame026_graph record012_frame026_links
def record012_frame027_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x1f23df7baf6debbd4794f11df3bb76cec9d73a973ee69cab916ced89af35a6aad3da5b48686cf59bb2e614c1d812ff5fabe152aa053ca714c295510a093e2794e89c1362684be9692a25044a87d0da1742683504a054027e8fa9ed396720e19c037c6e4ba9722dc5a8b29612be560a894a2824e89312423c46c8b11321c424820ff1f43cc778e51bc3686b0d31a232c638c11762e0590ac148280338660ca1902684c0961281d83a0720e01082003e0780a8140260480881001e0380680c0160280480600a01001800 } : Fields).get c.val)
theorem record012_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record012) (record012.maps 27) (record012.inverseMaps 27) record012_frame027_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record012) (record012.maps 27) (record012.inverseMaps 27) record012_frame027_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record012) (record012.maps 27) (record012.inverseMaps 27) record012_frame027_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record012) (record012.maps 27)
      (record012.inverseMaps 27) record012_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame027_links_0000 (interval_append _ 64 128 146 record012_frame027_links_0064 record012_frame027_links_0128))
theorem record012_frame027_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 27 :=
  of_group record012 27 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record012_frame027_indices record012_frame027_graph record012_frame027_links
def record012_frame028_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0780.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0780.count (({ width := 9, code := 0x2cd65b258ec561afd72b356a9d429b4ba4d1a89419f4ee7135994be592a9449647208ec6e33178ac4e05017fbf9f8fa7c3d5e4ef763a5cee571b85bedd6bb51a2ce65b218cc4613017cbc5b2d164b0572b136984aa491e8c452210c8441200fe7e3e9f0f67a3c9d8e670361a8d0663218cc4613017cbc5b2c154a24f2692c82401f8f85e2e168b0562a148a02e160a8502612088401e0e06830160a048200e050200c0400 } : Fields).get c.val)
theorem record012_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0780.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0780.localPairCheck (smallEmbedding record012) (record012.maps 28) (record012.inverseMaps 28) record012_frame028_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0780.localPairCheck (smallEmbedding record012) (record012.maps 28) (record012.inverseMaps 28) record012_frame028_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0780.localPairCheck (smallEmbedding record012) (record012.maps 28) (record012.inverseMaps 28) record012_frame028_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0780.localPairCheck (smallEmbedding record012) (record012.maps 28)
      (record012.inverseMaps 28) record012_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame028_links_0000 (interval_append _ 64 128 146 record012_frame028_links_0064 record012_frame028_links_0128))
theorem record012_frame028_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 28 :=
  of_group record012 28 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0780
    Papers.RationalityTen.SharedFrameCatalogue.group0780_facts record012_frame028_indices record012_frame028_graph record012_frame028_links
def record012_frame029_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0279.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0279.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0279.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0279.localPairCheck (smallEmbedding record012) (record012.maps 29) (record012.inverseMaps 29) record012_frame029_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0279.localPairCheck (smallEmbedding record012) (record012.maps 29) (record012.inverseMaps 29) record012_frame029_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0279.localPairCheck (smallEmbedding record012) (record012.maps 29) (record012.inverseMaps 29) record012_frame029_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0279.localPairCheck (smallEmbedding record012) (record012.maps 29)
      (record012.inverseMaps 29) record012_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame029_links_0000 (interval_append _ 64 128 146 record012_frame029_links_0064 record012_frame029_links_0128))
theorem record012_frame029_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 29 :=
  of_group record012 29 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0279
    Papers.RationalityTen.SharedFrameCatalogue.group0279_facts record012_frame029_indices record012_frame029_graph record012_frame029_links
def record012_frame030_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0234.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0234.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0234.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0234.localPairCheck (smallEmbedding record012) (record012.maps 30) (record012.inverseMaps 30) record012_frame030_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0234.localPairCheck (smallEmbedding record012) (record012.maps 30) (record012.inverseMaps 30) record012_frame030_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0234.localPairCheck (smallEmbedding record012) (record012.maps 30) (record012.inverseMaps 30) record012_frame030_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0234.localPairCheck (smallEmbedding record012) (record012.maps 30)
      (record012.inverseMaps 30) record012_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame030_links_0000 (interval_append _ 64 128 146 record012_frame030_links_0064 record012_frame030_links_0128))
theorem record012_frame030_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 30 :=
  of_group record012 30 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0234
    Papers.RationalityTen.SharedFrameCatalogue.group0234_facts record012_frame030_indices record012_frame030_graph record012_frame030_links
def record012_frame031_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0361.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0361.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0361.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0361.localPairCheck (smallEmbedding record012) (record012.maps 31) (record012.inverseMaps 31) record012_frame031_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0361.localPairCheck (smallEmbedding record012) (record012.maps 31) (record012.inverseMaps 31) record012_frame031_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0361.localPairCheck (smallEmbedding record012) (record012.maps 31) (record012.inverseMaps 31) record012_frame031_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0361.localPairCheck (smallEmbedding record012) (record012.maps 31)
      (record012.inverseMaps 31) record012_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame031_links_0000 (interval_append _ 64 128 146 record012_frame031_links_0064 record012_frame031_links_0128))
theorem record012_frame031_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 31 :=
  of_group record012 31 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0361
    Papers.RationalityTen.SharedFrameCatalogue.group0361_facts record012_frame031_indices record012_frame031_graph record012_frame031_links
def record012_frame032_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x2764e69c53766bcd498b2fe5acb195329a5149b929236434808b915e2744787f0ea1b431859096104177fcfe5f8beb7ccf81ba36e6d0d8daeb58688cf99ab30654c9990b19626c2d832ff5a8b3962ac0570ac956aa7544a714c28f4e89c535a664c4971062023f27c8f39e13b8748e59c33726c4c51842f85d4b61672c0560a994c2844e89992a2404688990c20a3f47b0ed1c636c6a0ce18c3003b8760ea1d02c8580ae158218420821001082003e0780a8140260480881001e0380680c0160280480600a01001800 } : Fields).get c.val)
theorem record012_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record012) (record012.maps 32) (record012.inverseMaps 32) record012_frame032_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record012) (record012.maps 32) (record012.inverseMaps 32) record012_frame032_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record012) (record012.maps 32) (record012.inverseMaps 32) record012_frame032_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record012) (record012.maps 32)
      (record012.inverseMaps 32) record012_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame032_links_0000 (interval_append _ 64 128 146 record012_frame032_links_0064 record012_frame032_links_0128))
theorem record012_frame032_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 32 :=
  of_group record012 32 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record012_frame032_indices record012_frame032_graph record012_frame032_links
def record012_frame033_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0x2833f9ecee73369a4ca612e95caa51269248a3f1e8e46a311689c4a210e8642a0f0682c0e02ff7ebe9eef579bc5deec74b99c8e26fb79b8d96bb55a4d16732d92c76230d82be5e2e96eb65aacd62af56aa950a6522893e9d4da652e95492410a83409fcf87a3b9d0e26d3519cc8602f170b4582a94ca04d2511886401e8e44a241188842200f878361a0c8602a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record012_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 33) (record012.inverseMaps 33) record012_frame033_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 33) (record012.inverseMaps 33) record012_frame033_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame033_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 33) (record012.inverseMaps 33) record012_frame033_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record012) (record012.maps 33)
      (record012.inverseMaps 33) record012_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame033_links_0000 (interval_append _ 64 128 146 record012_frame033_links_0064 record012_frame033_links_0128))
theorem record012_frame033_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 33 :=
  of_group record012 33 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record012_frame033_indices record012_frame033_graph record012_frame033_links
def record012_frame034_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x82e0981e04805fe7edf87d9f37c1ef7b1ea7a5e678de1755d3749cf731ca721c570dc06f5bc6c1af6b5ab69da3615836057e5ed775c16d5ad68591625795c56d58551505053f4f93b4dd334c12d4ad28491224591544d11435083c0ed3b0e9394e2380dd370d9354d2308c02f8bb2e0b42c0ac2aca62809d264942388c22887210801f47a1d8711b06819c620ec3a0e4380bc2e0b42c0a0270982506819060170541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record012_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record012) (record012.maps 34) (record012.inverseMaps 34) record012_frame034_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record012) (record012.maps 34) (record012.inverseMaps 34) record012_frame034_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame034_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record012) (record012.maps 34) (record012.inverseMaps 34) record012_frame034_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record012) (record012.maps 34)
      (record012.inverseMaps 34) record012_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame034_links_0000 (interval_append _ 64 128 146 record012_frame034_links_0064 record012_frame034_links_0128))
theorem record012_frame034_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 34 :=
  of_group record012 34 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record012_frame034_indices record012_frame034_graph record012_frame034_links
def record012_frame035_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0832.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0832.count (({ width := 9, code := 0x32992c8e431d8cc3e170982c05fafb7cbdde6f177b5daad367b3596c761b057ab95aa8d429d4da652a5b2b954a24b238ec6e35188a4461f0e86c2a11077d3e5f0f579bc9e0ee76badcee46d361acd4693416eb55a2c960ad562a952a752a89369a4c259269248231148942a09007e3d9e8f076399c8dc6b3499ccc623017c88432110470371b0d45e2e168b03e1e0e8702a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record012_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record012) (record012.maps 35) (record012.inverseMaps 35) record012_frame035_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record012) (record012.maps 35) (record012.inverseMaps 35) record012_frame035_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame035_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record012) (record012.maps 35) (record012.inverseMaps 35) record012_frame035_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record012) (record012.maps 35)
      (record012.inverseMaps 35) record012_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame035_links_0000 (interval_append _ 64 128 146 record012_frame035_links_0064 record012_frame035_links_0128))
theorem record012_frame035_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 35 :=
  of_group record012 35 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0832
    Papers.RationalityTen.SharedFrameCatalogue.group0832_facts record012_frame035_indices record012_frame035_graph record012_frame035_links
def record012_frame036_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0x33799cbe532792c6e2f1186c1e0aff7ebe5eef578b75b6d96ab459ec963b0d7ebb5baa54aa350a752e6b3398cba5b2c93c9a47228fc7a37198bc5a2b1383c160902803fdf8fb7cbddeaf3753a1cee67238594c962b0982bf5e2e972b659ac550a55228d3e9d4d255228e4521d08813e9f0f2773b1c8da6a33990c45e2c9587e3e1e8f06833190c4502713094381b0d0642a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record012_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record012) (record012.maps 36) (record012.inverseMaps 36) record012_frame036_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record012) (record012.maps 36) (record012.inverseMaps 36) record012_frame036_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame036_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record012) (record012.maps 36) (record012.inverseMaps 36) record012_frame036_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record012) (record012.maps 36)
      (record012.inverseMaps 36) record012_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame036_links_0000 (interval_append _ 64 128 146 record012_frame036_links_0064 record012_frame036_links_0128))
theorem record012_frame036_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 36 :=
  of_group record012 36 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record012_frame036_indices record012_frame036_graph record012_frame036_links
def record012_frame037_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0x3a9d3e873f9dcde4f1b89c2dfef775b9dbed767b1d2e9345a0cf6733597cae4f218ec260f0581c05f6c963b1586c15fad562ab53a8d3a9749a3d1687419b4d26530974b2552892c8e431e8b456291389445f6f878bb9d6e87338db8d96b34d96c761b017cb8592b554a65026d2e93482311085419f4ee72371a8ca602e9648642209006e361a8d0562a148a03e1e0e8702a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record012_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record012) (record012.maps 37) (record012.inverseMaps 37) record012_frame037_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record012) (record012.maps 37) (record012.inverseMaps 37) record012_frame037_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame037_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record012) (record012.maps 37) (record012.inverseMaps 37) record012_frame037_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record012) (record012.maps 37)
      (record012.inverseMaps 37) record012_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame037_links_0000 (interval_append _ 64 128 146 record012_frame037_links_0064 record012_frame037_links_0128))
theorem record012_frame037_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 37 :=
  of_group record012 37 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record012_frame037_indices record012_frame037_graph record012_frame037_links
def record012_frame038_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0733.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0733.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0733.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0733.localPairCheck (smallEmbedding record012) (record012.maps 38) (record012.inverseMaps 38) record012_frame038_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0733.localPairCheck (smallEmbedding record012) (record012.maps 38) (record012.inverseMaps 38) record012_frame038_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame038_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0733.localPairCheck (smallEmbedding record012) (record012.maps 38) (record012.inverseMaps 38) record012_frame038_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0733.localPairCheck (smallEmbedding record012) (record012.maps 38)
      (record012.inverseMaps 38) record012_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame038_links_0000 (interval_append _ 64 128 146 record012_frame038_links_0064 record012_frame038_links_0128))
theorem record012_frame038_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 38 :=
  of_group record012 38 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0733
    Papers.RationalityTen.SharedFrameCatalogue.group0733_facts record012_frame038_indices record012_frame038_graph record012_frame038_links
def record012_frame039_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0717.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0717.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0717.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0717.localPairCheck (smallEmbedding record012) (record012.maps 39) (record012.inverseMaps 39) record012_frame039_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0717.localPairCheck (smallEmbedding record012) (record012.maps 39) (record012.inverseMaps 39) record012_frame039_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame039_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0717.localPairCheck (smallEmbedding record012) (record012.maps 39) (record012.inverseMaps 39) record012_frame039_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0717.localPairCheck (smallEmbedding record012) (record012.maps 39)
      (record012.inverseMaps 39) record012_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame039_links_0000 (interval_append _ 64 128 146 record012_frame039_links_0064 record012_frame039_links_0128))
theorem record012_frame039_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 39 :=
  of_group record012 39 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0717
    Papers.RationalityTen.SharedFrameCatalogue.group0717_facts record012_frame039_indices record012_frame039_graph record012_frame039_links
def record012_frame040_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0179.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0179.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0179.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0179.localPairCheck (smallEmbedding record012) (record012.maps 40) (record012.inverseMaps 40) record012_frame040_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0179.localPairCheck (smallEmbedding record012) (record012.maps 40) (record012.inverseMaps 40) record012_frame040_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame040_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0179.localPairCheck (smallEmbedding record012) (record012.maps 40) (record012.inverseMaps 40) record012_frame040_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0179.localPairCheck (smallEmbedding record012) (record012.maps 40)
      (record012.inverseMaps 40) record012_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame040_links_0000 (interval_append _ 64 128 146 record012_frame040_links_0064 record012_frame040_links_0128))
theorem record012_frame040_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 40 :=
  of_group record012 40 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0179
    Papers.RationalityTen.SharedFrameCatalogue.group0179_facts record012_frame040_indices record012_frame040_graph record012_frame040_links
def record012_frame041_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1055.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1055.count (({ width := 8, code := 0xafadacabaaa9a7a6a5a4a3a2a09f9e9d9c9b9998979695949291908f8e8d8c8a8988878685838281807f7d7c7b7a79787675747372716f6e6d6c6b6a68676665646362605f5e5d5c5a5958575655535251504f4e4a49484746454341403f3d3b3a39373635343332302e2d2c2a28272621201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1055.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1055.localPairCheck (smallEmbedding record012) (record012.maps 41) (record012.inverseMaps 41) record012_frame041_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1055.localPairCheck (smallEmbedding record012) (record012.maps 41) (record012.inverseMaps 41) record012_frame041_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame041_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1055.localPairCheck (smallEmbedding record012) (record012.maps 41) (record012.inverseMaps 41) record012_frame041_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1055.localPairCheck (smallEmbedding record012) (record012.maps 41)
      (record012.inverseMaps 41) record012_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame041_links_0000 (interval_append _ 64 128 146 record012_frame041_links_0064 record012_frame041_links_0128))
theorem record012_frame041_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 41 :=
  of_group record012 41 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1055
    Papers.RationalityTen.SharedFrameCatalogue.group1055_facts record012_frame041_indices record012_frame041_graph record012_frame041_links
def record012_frame042_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0353.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0353.count (({ width := 8, code := 0xc1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a78767472706e6c6a686664625c5a58565452504e4c4a48464442403e3c3a38363432302e2c2a282621201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0353.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record012) (record012.maps 42) (record012.inverseMaps 42) record012_frame042_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record012) (record012.maps 42) (record012.inverseMaps 42) record012_frame042_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame042_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record012) (record012.maps 42) (record012.inverseMaps 42) record012_frame042_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0353.localPairCheck (smallEmbedding record012) (record012.maps 42)
      (record012.inverseMaps 42) record012_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame042_links_0000 (interval_append _ 64 128 146 record012_frame042_links_0064 record012_frame042_links_0128))
theorem record012_frame042_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 42 :=
  of_group record012 42 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0353
    Papers.RationalityTen.SharedFrameCatalogue.group0353_facts record012_frame042_indices record012_frame042_graph record012_frame042_links
def record012_frame043_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0716.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0716.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0716.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0716.localPairCheck (smallEmbedding record012) (record012.maps 43) (record012.inverseMaps 43) record012_frame043_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0716.localPairCheck (smallEmbedding record012) (record012.maps 43) (record012.inverseMaps 43) record012_frame043_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame043_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0716.localPairCheck (smallEmbedding record012) (record012.maps 43) (record012.inverseMaps 43) record012_frame043_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0716.localPairCheck (smallEmbedding record012) (record012.maps 43)
      (record012.inverseMaps 43) record012_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame043_links_0000 (interval_append _ 64 128 146 record012_frame043_links_0064 record012_frame043_links_0128))
theorem record012_frame043_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 43 :=
  of_group record012 43 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0716
    Papers.RationalityTen.SharedFrameCatalogue.group0716_facts record012_frame043_indices record012_frame043_graph record012_frame043_links
def record012_frame044_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0177.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0177.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame044_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0177.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame044_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0177.localPairCheck (smallEmbedding record012) (record012.maps 44) (record012.inverseMaps 44) record012_frame044_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame044_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0177.localPairCheck (smallEmbedding record012) (record012.maps 44) (record012.inverseMaps 44) record012_frame044_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame044_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0177.localPairCheck (smallEmbedding record012) (record012.maps 44) (record012.inverseMaps 44) record012_frame044_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame044_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0177.localPairCheck (smallEmbedding record012) (record012.maps 44)
      (record012.inverseMaps 44) record012_frame044_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame044_links_0000 (interval_append _ 64 128 146 record012_frame044_links_0064 record012_frame044_links_0128))
theorem record012_frame044_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 44 :=
  of_group record012 44 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0177
    Papers.RationalityTen.SharedFrameCatalogue.group0177_facts record012_frame044_indices record012_frame044_graph record012_frame044_links
def record012_frame045_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0434.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0434.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame045_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0434.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame045_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0434.localPairCheck (smallEmbedding record012) (record012.maps 45) (record012.inverseMaps 45) record012_frame045_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame045_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0434.localPairCheck (smallEmbedding record012) (record012.maps 45) (record012.inverseMaps 45) record012_frame045_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame045_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0434.localPairCheck (smallEmbedding record012) (record012.maps 45) (record012.inverseMaps 45) record012_frame045_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame045_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0434.localPairCheck (smallEmbedding record012) (record012.maps 45)
      (record012.inverseMaps 45) record012_frame045_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame045_links_0000 (interval_append _ 64 128 146 record012_frame045_links_0064 record012_frame045_links_0128))
theorem record012_frame045_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 45 :=
  of_group record012 45 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0434
    Papers.RationalityTen.SharedFrameCatalogue.group0434_facts record012_frame045_indices record012_frame045_graph record012_frame045_links
def record012_frame046_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0524.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0524.count (({ width := 9, code := 0x2c360af576b95babd5aa952a853a994ba4d1e8b439dcea71369a4ca612f96cae532791486411f8f4721d0d8642e150982c0e02ff7ebedf2f77abcde2ef73b95c6e16fb75b6d96bb55a6d16632d94c96431d70b7592bd5cab54aa146a04fa712e96492411e8a4320d007d3d1dce871379b8d46833988bc5b2c154a44f2612474391c0dc6431180bc4c251208c3c1d0e06c2a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record012_frame046_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0524.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame046_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record012) (record012.maps 46) (record012.inverseMaps 46) record012_frame046_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame046_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record012) (record012.maps 46) (record012.inverseMaps 46) record012_frame046_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame046_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record012) (record012.maps 46) (record012.inverseMaps 46) record012_frame046_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame046_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record012) (record012.maps 46)
      (record012.inverseMaps 46) record012_frame046_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame046_links_0000 (interval_append _ 64 128 146 record012_frame046_links_0064 record012_frame046_links_0128))
theorem record012_frame046_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 46 :=
  of_group record012 46 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0524
    Papers.RationalityTen.SharedFrameCatalogue.group0524_facts record012_frame046_indices record012_frame046_graph record012_frame046_links
def record012_frame047_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0223.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0223.count (({ width := 9, code := 0x2070280c01fefe7dbe9f0f67a3c9e2f0773b1d4e871b89c0de6e369b2d86b351a4d066b3196ca64b217cbd5e2ed74b95b2d566b157ab558ab54a9d4aa34f27536994ba55289348a3d1a8b4421d0c854220cf4793b9d4e671381bcda6b3499ccc6531984be5d2d964ae55299449e4d2612c92472290c823f1e8ec72371a8cc6230178b8562a148a04a24118883e1e0e8702a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record012_frame047_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0223.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame047_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record012) (record012.maps 47) (record012.inverseMaps 47) record012_frame047_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame047_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record012) (record012.maps 47) (record012.inverseMaps 47) record012_frame047_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame047_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record012) (record012.maps 47) (record012.inverseMaps 47) record012_frame047_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame047_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0223.localPairCheck (smallEmbedding record012) (record012.maps 47)
      (record012.inverseMaps 47) record012_frame047_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame047_links_0000 (interval_append _ 64 128 146 record012_frame047_links_0064 record012_frame047_links_0128))
theorem record012_frame047_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 47 :=
  of_group record012 47 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0223
    Papers.RationalityTen.SharedFrameCatalogue.group0223_facts record012_frame047_indices record012_frame047_graph record012_frame047_links
def record012_frame048_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0324.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0324.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame048_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0324.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame048_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0324.localPairCheck (smallEmbedding record012) (record012.maps 48) (record012.inverseMaps 48) record012_frame048_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame048_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0324.localPairCheck (smallEmbedding record012) (record012.maps 48) (record012.inverseMaps 48) record012_frame048_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame048_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0324.localPairCheck (smallEmbedding record012) (record012.maps 48) (record012.inverseMaps 48) record012_frame048_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame048_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0324.localPairCheck (smallEmbedding record012) (record012.maps 48)
      (record012.inverseMaps 48) record012_frame048_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame048_links_0000 (interval_append _ 64 128 146 record012_frame048_links_0064 record012_frame048_links_0128))
theorem record012_frame048_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 48 :=
  of_group record012 48 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0324
    Papers.RationalityTen.SharedFrameCatalogue.group0324_facts record012_frame048_indices record012_frame048_graph record012_frame048_links
def record012_frame049_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0278.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0278.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame049_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0278.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame049_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0278.localPairCheck (smallEmbedding record012) (record012.maps 49) (record012.inverseMaps 49) record012_frame049_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame049_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0278.localPairCheck (smallEmbedding record012) (record012.maps 49) (record012.inverseMaps 49) record012_frame049_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame049_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0278.localPairCheck (smallEmbedding record012) (record012.maps 49) (record012.inverseMaps 49) record012_frame049_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame049_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0278.localPairCheck (smallEmbedding record012) (record012.maps 49)
      (record012.inverseMaps 49) record012_frame049_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame049_links_0000 (interval_append _ 64 128 146 record012_frame049_links_0064 record012_frame049_links_0128))
theorem record012_frame049_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 49 :=
  of_group record012 49 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0278
    Papers.RationalityTen.SharedFrameCatalogue.group0278_facts record012_frame049_indices record012_frame049_graph record012_frame049_links
def record012_frame050_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x180ebf35ee2f21764b9d5a12cb562eb055792b79590ab45502a314eea624dca6953289814b72571292935490a43d1fa8ea44421d90c885242120c0da66bf3541a50cfc66930717e4bc65d12df16a8b285802b61560a8652e24291c48c044d21d10a082a4011f68f6c7923b61aa0d0866031e1870bf0472232115889043a21610788204021fa0f987b03921c20dd86d035a1a60ce865831e1880c085e82e616c0b005642a414b0a204f426812d093047c230111085040c0f607a03c81e00b205802b8158086042020810004202000f807802a0140098048022010007803801a00c00580280120060028010006000 } : Fields).get c.val)
theorem record012_frame050_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame050_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 50) (record012.inverseMaps 50) record012_frame050_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame050_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 50) (record012.inverseMaps 50) record012_frame050_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame050_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 50) (record012.inverseMaps 50) record012_frame050_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame050_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 50)
      (record012.inverseMaps 50) record012_frame050_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame050_links_0000 (interval_append _ 64 128 146 record012_frame050_links_0064 record012_frame050_links_0128))
theorem record012_frame050_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 50 :=
  of_group record012 50 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame050_indices record012_frame050_graph record012_frame050_links
def record012_frame051_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x60d6055fe5f85f05ea5d15cc5c25bc5b25ab5a159c59158b57e57952c5255195125074fe4f34ef4e54e14d54ce49548f48347846c4653d43cd3c73c03ba3b139839138d38337d37236836135c35034a3402f32eb2e42d82d02c52ba2b42af2a529f29525c25324a23d23522c1ac1a81a219c19619118b18718117c17717115715414f14914313d13613012b12712311d11611110c10a1051000fb0f60ee0e80e30de0d80d20cd0c707307207107005205105004f04204104003f02102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame051_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame051_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record012) (record012.maps 51) (record012.inverseMaps 51) record012_frame051_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame051_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record012) (record012.maps 51) (record012.inverseMaps 51) record012_frame051_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame051_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record012) (record012.maps 51) (record012.inverseMaps 51) record012_frame051_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame051_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record012) (record012.maps 51)
      (record012.inverseMaps 51) record012_frame051_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame051_links_0000 (interval_append _ 64 128 146 record012_frame051_links_0064 record012_frame051_links_0128))
theorem record012_frame051_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 51 :=
  of_group record012 51 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record012_frame051_indices record012_frame051_graph record012_frame051_links
def record012_frame052_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x5f05ec5e85e05d95d05be5b85b35ad5a559859058858257b57356652151851250d5044f84f04e84e04d94d04c548c4854804784704663e93e43e03d83d13cc3b63b13ab3a539a39538938137a37336836231931130a3052f92f32e92e02d82d12c62be28427d27827026625f1ee1e71e11de1d81d11cb1c51bf1bc1b71b018f18918418017a17316a16415c15515114b14313d13312c12712311d11610d1050fd0f70f10e90e10dc07207107006f05305205105004003f03e03d02102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record012_frame052_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame052_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record012) (record012.maps 52) (record012.inverseMaps 52) record012_frame052_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame052_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record012) (record012.maps 52) (record012.inverseMaps 52) record012_frame052_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame052_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record012) (record012.maps 52) (record012.inverseMaps 52) record012_frame052_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame052_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record012) (record012.maps 52)
      (record012.inverseMaps 52) record012_frame052_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame052_links_0000 (interval_append _ 64 128 146 record012_frame052_links_0064 record012_frame052_links_0128))
theorem record012_frame052_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 52 :=
  of_group record012 52 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record012_frame052_indices record012_frame052_graph record012_frame052_links
def record012_frame053_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x23f1e8ec72371a8cc622f168ac52271288c421f0e8441e0d058240e05007f3f1f4f876bb1d6ea74ba1bcdd6e36db4d96c35dacd56a34da4d16833d9ccd63b198ac461b0982bf5eaed72b7562ad54a95429d389a4c259289248239188a44218f87a3c1d8e872379b0d26632188c05e2d964ae55299449c4b2411486411f8f46833190c452281389848231108432180b858281309044200f07034180b050241006028100600 } : Fields).get c.val)
theorem record012_frame053_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame053_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record012) (record012.maps 53) (record012.inverseMaps 53) record012_frame053_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame053_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record012) (record012.maps 53) (record012.inverseMaps 53) record012_frame053_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame053_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record012) (record012.maps 53) (record012.inverseMaps 53) record012_frame053_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame053_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record012) (record012.maps 53)
      (record012.inverseMaps 53) record012_frame053_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame053_links_0000 (interval_append _ 64 128 146 record012_frame053_links_0064 record012_frame053_links_0128))
theorem record012_frame053_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 53 :=
  of_group record012 53 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record012_frame053_indices record012_frame053_graph record012_frame053_links
def record012_frame054_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0x25b2c95caa532893c9a4b2491c8a43208fc7a3b1c8b456291389446210e8642a11067d3e5f0f77b3d5d0e773395c8e371385c0df6f375b8db6d365b0d768b419ece66b3196c963b1586c15aad166b258ac144a04f27134984b251249047231027f3e9ecf277399c0da6a34198c8622f974b6592b954a24e259208842200f86833190c452281389848231108432180b858281309044200f07034180b050241006028100600 } : Fields).get c.val)
theorem record012_frame054_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame054_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record012) (record012.maps 54) (record012.inverseMaps 54) record012_frame054_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame054_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record012) (record012.maps 54) (record012.inverseMaps 54) record012_frame054_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame054_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record012) (record012.maps 54) (record012.inverseMaps 54) record012_frame054_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame054_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record012) (record012.maps 54)
      (record012.inverseMaps 54) record012_frame054_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame054_links_0000 (interval_append _ 64 128 146 record012_frame054_links_0064 record012_frame054_links_0128))
theorem record012_frame054_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 54 :=
  of_group record012 54 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record012_frame054_indices record012_frame054_graph record012_frame054_links
def record012_frame055_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0335.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0335.count (({ width := 9, code := 0x2190b8542611078341609038140600ff7f3f5f8fb7b3d5e8f3793c5e0ee763a9d0e67037dbcdd6e36da2d067b399acc65b2992c863b198ac461b0982c05dae972b85bad96ab358abd5aab52a9146a250a812a9348a3d1a8b44a1d0a83409fcea73389bcda6b34194c45f2e96cb2572a148a04e261288e44208f8783a1c0d8602f170b44e261289044211007c32180b858281309044200f07034180b050241006028100600 } : Fields).get c.val)
theorem record012_frame055_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0335.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame055_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record012) (record012.maps 55) (record012.inverseMaps 55) record012_frame055_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame055_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record012) (record012.maps 55) (record012.inverseMaps 55) record012_frame055_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame055_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record012) (record012.maps 55) (record012.inverseMaps 55) record012_frame055_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame055_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record012) (record012.maps 55)
      (record012.inverseMaps 55) record012_frame055_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame055_links_0000 (interval_append _ 64 128 146 record012_frame055_links_0064 record012_frame055_links_0128))
theorem record012_frame055_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 55 :=
  of_group record012 55 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0335
    Papers.RationalityTen.SharedFrameCatalogue.group0335_facts record012_frame055_indices record012_frame055_graph record012_frame055_links
def record012_frame056_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0272.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0272.count (({ width := 9, code := 0x24f269248e45208fc76391b8cc622f158a44e231085c26110782c120701803fdfafc7bbd9e8f3793c1d6ea7439dcce471b85c0df6eb71b6d96c35daad467b3598cb64b218ec56230d82c05dae970b75b2d15cab54a9d48a25027536994b2510c83409fcf87a3b1c8dc6a33990c25e2d960ac542893c9647218fc78391b0cc4a241188842200f878381b0d06430170b0542612088401e0e06830160a048200e050200c0400 } : Fields).get c.val)
theorem record012_frame056_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0272.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame056_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record012) (record012.maps 56) (record012.inverseMaps 56) record012_frame056_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame056_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record012) (record012.maps 56) (record012.inverseMaps 56) record012_frame056_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame056_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record012) (record012.maps 56) (record012.inverseMaps 56) record012_frame056_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame056_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0272.localPairCheck (smallEmbedding record012) (record012.maps 56)
      (record012.inverseMaps 56) record012_frame056_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame056_links_0000 (interval_append _ 64 128 146 record012_frame056_links_0064 record012_frame056_links_0128))
theorem record012_frame056_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 56 :=
  of_group record012 56 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0272
    Papers.RationalityTen.SharedFrameCatalogue.group0272_facts record012_frame056_indices record012_frame056_graph record012_frame056_links
def record012_frame057_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0172.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0172.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame057_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0172.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame057_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0172.localPairCheck (smallEmbedding record012) (record012.maps 57) (record012.inverseMaps 57) record012_frame057_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame057_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0172.localPairCheck (smallEmbedding record012) (record012.maps 57) (record012.inverseMaps 57) record012_frame057_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame057_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0172.localPairCheck (smallEmbedding record012) (record012.maps 57) (record012.inverseMaps 57) record012_frame057_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame057_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0172.localPairCheck (smallEmbedding record012) (record012.maps 57)
      (record012.inverseMaps 57) record012_frame057_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame057_links_0000 (interval_append _ 64 128 146 record012_frame057_links_0064 record012_frame057_links_0128))
theorem record012_frame057_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 57 :=
  of_group record012 57 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0172
    Papers.RationalityTen.SharedFrameCatalogue.group0172_facts record012_frame057_indices record012_frame057_graph record012_frame057_links
def record012_frame058_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0299.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0299.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record012_frame058_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0299.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame058_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0299.localPairCheck (smallEmbedding record012) (record012.maps 58) (record012.inverseMaps 58) record012_frame058_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame058_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0299.localPairCheck (smallEmbedding record012) (record012.maps 58) (record012.inverseMaps 58) record012_frame058_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame058_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0299.localPairCheck (smallEmbedding record012) (record012.maps 58) (record012.inverseMaps 58) record012_frame058_indices (Fin.ofNat record012.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record012_frame058_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0299.localPairCheck (smallEmbedding record012) (record012.maps 58)
      (record012.inverseMaps 58) record012_frame058_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record012_frame058_links_0000 (interval_append _ 64 128 146 record012_frame058_links_0064 record012_frame058_links_0128))
theorem record012_frame058_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 58 :=
  of_group record012 58 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0299
    Papers.RationalityTen.SharedFrameCatalogue.group0299_facts record012_frame058_indices record012_frame058_graph record012_frame058_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (Fin.cases (record012_frame008_supported hcells) (Fin.cases (record012_frame009_supported hcells) (Fin.cases (record012_frame010_supported hcells) (Fin.cases (record012_frame011_supported hcells) (Fin.cases (record012_frame012_supported hcells) (Fin.cases (record012_frame013_supported hcells) (Fin.cases (record012_frame014_supported hcells) (Fin.cases (record012_frame015_supported hcells) (Fin.cases (record012_frame016_supported hcells) (Fin.cases (record012_frame017_supported hcells) (Fin.cases (record012_frame018_supported hcells) (Fin.cases (record012_frame019_supported hcells) (Fin.cases (record012_frame020_supported hcells) (Fin.cases (record012_frame021_supported hcells) (Fin.cases (record012_frame022_supported hcells) (Fin.cases (record012_frame023_supported hcells) (Fin.cases (record012_frame024_supported hcells) (Fin.cases (record012_frame025_supported hcells) (Fin.cases (record012_frame026_supported hcells) (Fin.cases (record012_frame027_supported hcells) (Fin.cases (record012_frame028_supported hcells) (Fin.cases (record012_frame029_supported hcells) (Fin.cases (record012_frame030_supported hcells) (Fin.cases (record012_frame031_supported hcells) (Fin.cases (record012_frame032_supported hcells) (Fin.cases (record012_frame033_supported hcells) (Fin.cases (record012_frame034_supported hcells) (Fin.cases (record012_frame035_supported hcells) (Fin.cases (record012_frame036_supported hcells) (Fin.cases (record012_frame037_supported hcells) (Fin.cases (record012_frame038_supported hcells) (Fin.cases (record012_frame039_supported hcells) (Fin.cases (record012_frame040_supported hcells) (Fin.cases (record012_frame041_supported hcells) (Fin.cases (record012_frame042_supported hcells) (Fin.cases (record012_frame043_supported hcells) (Fin.cases (record012_frame044_supported hcells) (Fin.cases (record012_frame045_supported hcells) (Fin.cases (record012_frame046_supported hcells) (Fin.cases (record012_frame047_supported hcells) (Fin.cases (record012_frame048_supported hcells) (Fin.cases (record012_frame049_supported hcells) (Fin.cases (record012_frame050_supported hcells) (Fin.cases (record012_frame051_supported hcells) (Fin.cases (record012_frame052_supported hcells) (Fin.cases (record012_frame053_supported hcells) (Fin.cases (record012_frame054_supported hcells) (Fin.cases (record012_frame055_supported hcells) (Fin.cases (record012_frame056_supported hcells) (Fin.cases (record012_frame057_supported hcells) (Fin.cases (record012_frame058_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record012_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173
