module
prelude
public import GraphInputsRow30Part00032Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups009Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups080Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73272770c6c569968f66765f65164963562f62060e6055f75d85cf57b55b54252a4d84ba49e49548b48147746045845245044b4444404393fb3f63dd3ca3c237b37335532e31f30c2c52ad2a527e27326f26025c24a23c23622421b20b2021f91f41f01c51aa19518017016b16415f13311e10e1090fc0f70d50c60c00bf0bd0ad0a109407006805e05805505204404103903102902202001c00e00d009007002001000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x1fcbf37cef71e53ac742e29bb35b62ec0d742cd578add562a8546a61462854e49892e24b4909091e2384588a91121b42c845022003f47ccf41d83a2738e09b534c688c59842f45c8b61662a8534a213e2644808b11220a3ec768ea17a2dc528920e016c2b85009c1282484808a1101f03c0700d81782b0480880f01d0380580780d0120200380400600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x64031e58e0c60602afe57a8bc25b1ad5d664b2055aaa8d4cea5150ea81529a91b44d21a10688274019eccf4875a3a31c24df46b034e195cc7c61230016ccb3e53027e128c8de45922410c084840d1f68d886a43401988c9461a2fd1608ac453e29014209b04b822110d87d83c81cd0dc06a431a17b09604881de0e5059827c12a08e04682300d606902e01680ae05502a00c8062023011007803a01c00a805001a0080038008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x67a33b59c8cce635315d848c0d5d52e616d6b5855529e147ca2c4ffa7b127c90c46422d912288442c2004fe479f3c71d48e826f937499b0c505fd2f61690b28517269928c912474230911c8724252018db86b63421968c7c6062ef1560a7051627b13789684961fb0f787243721a80cc06302ee16808c04301ce0e1059827c12a08e04682300d606902e01680ae05502a00c8062023011007803a01c00a805001a0080038008002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1094.count (({ width := 9, code := 0xb8dc2df6eb6db2d568b258ec35fa9d329348a351271319347e391b8d46631158a446210d86405f4f87bbd1e6e870b5da0ce66b3196ca64b057ebb5c2d560ad5128138994b2451c803e9d4e66f361a4c861299408a421f0f4783b1d0e46431168b0562a148803e1a0c8602e160a04c1a08038080200 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1094
    Papers.RationalityTen.SharedFrameCatalogue.group1094_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1087.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1087.count (({ width := 7, code := 0xcf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1087.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1087.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1087.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1087.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1087
    Papers.RationalityTen.SharedFrameCatalogue.group1087_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa1fa0ca029fc9df9d99ca9c398f98897696c8fe8d68ac8a088887d7f07bf7497136af69969067767065564a62b6235fe5f25985625505485215144b74804303f53c139e3963913863793243173062f62ec2d82cc29a28a2762682602482381e41d81bd1b11a11921871721641161080d50cb0a109708f08808708606906705a05805505305203203102302201e01d01c01501400d008007002001000 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame005_links_0000 record004_frame005_links_0064)
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6a769b69869367867366265963763261e6145cb5ac58f58957456b5235054c74a746945e45443e43941840f3fd3f83d23c839136535534f32a3212e92bf28d25f23822221a21320f2091da1d11c91c01ba1b51ae19118918017817116b16513f13612912311d11711110c1070e50de0c60be0a509909108a08908806906705a05805505305203203102302201e01d01c01501400d008007002001000 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame006_links_0000 record004_frame006_links_0064)
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x92d246474878e91c62f45888b10a19c2e800fb1ef3d879cf29cd3886c4d3996324632c25832ea5cab656b2bd56ea593ea744dc9692b22f4267d4ee9c63746d4d89af354618c097b2ec5c8b5161296514a013b26a4b4921082043ec7a8f11d639c710de1862f0548a61202204107c0f61e82f85e0a61442704c0960c0178230440780e81c02a0500680800e00800800 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame007_links_0000 record004_frame007_links_0064)
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0990.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0990.count (({ width := 7, code := 0xcf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0990.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0990.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0990.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0990.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record004_frame008_links_0000 record004_frame008_links_0064)
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0990
    Papers.RationalityTen.SharedFrameCatalogue.group0990_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0x1daebf4b97bcd86b34f9bc6e22ff77b85b6d566add52a54da3512813f9ecde632f95c92451d8dc661f0d8542202fd7b3bdcee16d349a2c45e2dd56a74c25112813e1bcd65e2d15094492410478381a0cc642f170b4582b1489c482310078381b0d058260f068241007018080200 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0x6bf59abd4e9b49a0cee471987c0ddee571b358abd5aaad1a833e9dcde653095496431d8c45225108642607017f3e1e8f2773b1cae36fb6daed56833590c35f2e168b05328938994923d0a823d1d4e26832974b457220f47235188c05e2c158a852261208c42200f07432180b858260f068241007018080200 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x13c6714cf98d2ca4fc838ed15a26c4086904a013f57a4f2ddf3b3746dbdacb4f67aca19031c600bdd78ae75b8b29612ba560a714928d4fa9b532a5f4aa9391ca3545c8790aa093ea7bcf11d53826acce9912e0574a71492824f09311e2123d8760d81a0314600bb0f01a42e85209c134260490901181f83906c0d01682b04a0880f01d0380580980f01a0240400700600800800 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0520.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0520.count (({ width := 9, code := 0x73f9dcbe571b87bbdc6bb55a6d16772d92c5e1b0980bcda6c35cac54ea14ea350a833e9d4e66f3498caa4f2691c7a371a8bc52190a83409fafa783adcce06d3499cc95e2d95cab5328d329647221067a3b9c8de6c2a1348c3f1e0ec74371b0d46630170b04e2611880381b0d058260f068241007018080200 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0520
    Papers.RationalityTen.SharedFrameCatalogue.group0520_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x1a073d670cd78cf09e03bed7aaf15dfb8b706dd5acb47646c0d7cacf552a4d3ca5746e834f29d333645c668b90d21541d821005fc3f57b4f51e4bbd760e7dc83886e4d95adb4e686cdd93319626bf5642af554a3143a7548c840ff1f838e6f0d518e2f659c9c92e2323fc768db120220428831001f8318560a4144280310440780e81c03005c0a81001a0240400700600800800 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xba7732dfdbab6f6a2c1568aaf53ea552ca37422824f69a33165bca492b24640c5f8a91221a4027a4f11de3ac716de9bb3686a8d2596b1060ec057b2e35b0aed4fa744b094915a21434844fc9f33806d0d39a030c5f8ba96d2cc580a693523e450869062003e4798e81ac324588aa10e214408800f61a43185a0a81442784e0860c8188230440780e81c02a0400680800e00800800 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x44a7c6f1de0bb9762e5dc6b6a6cad81adb4d652c3d722e052aa4538a6c4cc939202334388650820a3c6770da1a833a608bd16d2ba554a81472724cc7c8f51de3a0700d61a031c610bc1642b4540a311c2043d0770cc18c2e8560a21402684c0720d01882f05a0ac150220420740e01902e0580800d0160200380400600800800 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xbde51ba7b13cc9c64d4a56d2708b445022450fa8593f89e94e3c7123291904bec5d92e11630ae055728313ec9d04dd24211b882e3f11ea8e286d433d17b0b845aa2c01528a503d61df0e707083501860bb054028413208704001e80e7054025011808803601a40c605a02a81500a205001c80d006202f01680ac054022010807403801900b805802000d005802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1cb4e4d723b90dc80e3c71b38b9c46e1d70737fdbe8dee6efb521a8ad40668332d976c6763131496f0b715b3abb55b8ac1546a9f14c29b64d2a54528090d482a3fd1ee8be45421910a484441920910248043f91e94f207593a21cc4e5672538f1c5cdce6d435b9a9cd2e6873389958c8c6363131840b1257929a14909f44ee275131495a47722d914889042c2118e8c6f234318c8bfc5ee2f01608a1c4bc24e11e08904282020b4857c27012e09303d81d00dd06982a414609904181f40e6028012007c02400e0048008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1d9eec375e3ac9d54e9f7443a05ceee6f7323951c9ee4c723b675b34d8b68234059e4caf655b299798bb85cbaca962caf55682b2157ca0a4f926312fa945497a4812188d946522490f886d42ca13508a83f41b9fccfc07b13d11e1cee87613a71cd0e0e6f836e9b28d6e6a434519d8ce06693311968b985b92b39560a5650827f136899649e23d91c48ce45b22b8f1471e3541958c085e02db1598a284c224f11d08b044821c0b3855825c12408c03c41ce0db06902a414609904181f40e6028012007c02400e0048008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x204406807001ff3fb7f2fd9f9bf17dcfadf43e67c6f4de8bce776ee5db3a774ae89c137e6f0d95b0b5b69ed2da2b3465ec4986af85e6bc1752de5b2b115fabc56cac956aaa548a694a28a5089f13ca754e29b131a5d4aa9492724a48a8f91da374668b91121d4067f8f59e33c275ce91bf36e6d4d91aa350654bf96a2a8518a093b25c460851051fe3e47a0ee1822ec550a413c240450841021e03a06f0ca1802d0260440740900e01200800800 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xfbbecfa7e7f97e2f83ddf6fd9f5bd3f47cff33bceebb7e93a2e7f8fe378ada765d7f4cd2342cdf33cb71cc5efdbe2e7b8adfb66ccb1eb6ac6aeaa2a4a7e9ca5a8ca1a7c9da6e9ae6798e5e9564f91e449023c8de308b6298962084e0d7d5ef77dd7755ca711b46b1aa69d9f675895d561535404ed354a11441d023f0f63c4eb304bb2a8a42789022884204771c86c1885d15c260881d0480e0240200400 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x1d7bae75aeb1d5baa752ea1d3ba674ae89cfb9e73ae45c838f702e01bfb6f6dcdb1a0b3e676cc59732a63ec6989ae95ccb55692c7586af95c2a8548a5547a895069f53ba714d69792e2544a4935252474889051c2364628b5152274468790c21341c820ed9d73886f4d89a4342658c89822ea5ccb69622c25209e1302464648990a1fe3c8748e41b8354688ca14c28c4b893120218418821001d83a8700d019c3102804807c0900e01200800800 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame005_links_0000 record010_frame005_links_0064)
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x2e8dceb9972ee55c9b9171ae1dc2b836fededbbb7565ecad92ae35c2b655bab55568750ba0d3a6724dd99d32a5ec6d8cb10e1e41e82d03a03bf47dcf6de83ca77eeddd83a673ae1dc0b786e8dadb2b616bad5da4b44672cb994321638c4d87b08602bd5602bb53ea613fa704da9752aa3d4548950f207406748df1ad33e644c59842ea578a694426c4ac901171c0368630c217a2b0538a4140238460860f01d83802804807c0900e01200800800 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame006_links_0000 record010_frame006_links_0064)
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0529.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0529.count (({ width := 8, code := 0xebeae9e8e7e6e5e4e3e2e1e0dfdedddbdad9d8d7d6d5d4d3d1d0cfcecdcccbcac9c4c2bebcb9b8b7b5b2b0adacaba9a7a6a5a3a09e9c9a989796959492908e8d8c8b8a88878685847f7d79777473726f6d6a69686665645f5b59555453514f4b4a49474645433b3a3736353231302f2c2b2925242212110f0a0907020100 } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0529.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0529.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0529.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0529.localPairCheck (smallEmbedding record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame007_links_0000 record010_frame007_links_0064)
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0529
    Papers.RationalityTen.SharedFrameCatalogue.group0529_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
def record010_frame008_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0527.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0527.count (({ width := 8, code := 0xebeae9e8e7e6e5e4e3e2e1e0dfdedddbdad9d8d7d6d5d4d3d1d0cfcecdcccbcac9c4c2bebcb9b8b7b5b2b0adacaba9a7a6a5a3a09e9c9a989796959492908e8d8c8b8a88878685847f7d79777473726f6d6a69686665645f5b59555453514f4b4a49474645433b3a3736353231302f2c2b2925242212110f0a0907020100 } : Fields).get c.val)
theorem record010_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0527.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0527.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0527.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record010_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0527.localPairCheck (smallEmbedding record010) (record010.maps 8)
      (record010.inverseMaps 8) record010_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record010_frame008_links_0000 record010_frame008_links_0064)
theorem record010_frame008_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 8 :=
  of_group record010 8 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0527
    Papers.RationalityTen.SharedFrameCatalogue.group0527_facts record010_frame008_indices record010_frame008_graph record010_frame008_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (Fin.cases (record010_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8db8d68d28cc8c98c38af8a889e8698508498138007f47ea7da7ce7c476b76175770f7046f76d766161b6106035c55a859759358c57b5775054fe4f44ab49648b4603dd3a338e38334033232431b3173093002a728c24f23421b21720f1ee1d31b21a71a018917f15813d11610c0f90ee0e70ce0ca0c60c20b10af0a30a109909708507f06f05c05704b04503602301e014010008001000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x77477277177076f76b76876576374d74173e72170f6ff6f46e46d96cf66565464b6196106045ed57854253a5304e54c54a449f49347947342341b40a3dd3cd3c43a432e3072f72ef29a28b26f25c2592422321f71e81cd1bc1ad1a91a118917816515c15414313a1231171020fa0ed0e50de0c60be0b90b40a80a709d09b09309208107d06d05a05504b04503602301e014010008001000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x38ee338be2787e1381df77cdb368d9356d4f51d374ad1b42c8f1ac5701bfefcbd2cdad6b1ab6879de709b265972598e6378ba1a84e0f801d2705bd6ed9b6498b6057e5dd70539474d92d491204690d410f53cceb380dd328c12c4a927c9825c872087f1ec731c86e1b4691a05f1705111c420ec380b823078140400800400 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0490.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0490.count (({ width := 8, code := 0xdfdddcdad8d6d4d1d0cecdcac8c6c4c3c1bfbebbb8b7b2b0aeaca3a19f9e9a97959392908e8a89868482807e76726f6d69666562615f5d5856545251504f4e4d4a484644423f3e3b383735332f2d2b2927262322201f1918151312100f0d0b090504020100 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0490
    Papers.RationalityTen.SharedFrameCatalogue.group0490_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0487.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0487.count (({ width := 7, code := 0x64c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0487.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0487.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0487.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0487.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0487
    Papers.RationalityTen.SharedFrameCatalogue.group0487_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0476.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0476.count (({ width := 7, code := 0x64c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0476.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0476.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0476.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0476.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0476
    Papers.RationalityTen.SharedFrameCatalogue.group0476_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0469.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0469.count (({ width := 8, code := 0x959392908e8c8a87868483807e7d7c7b7a79787572716f6e6d6c69676564605e5d5c5b5a59565552504e4c4a46454443413f3e3d3c3b3a37363534333231302f2d2c2b2a29272624232221201e1d1c1b19181615141311100e0d0c0b0a0807060504020100 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0469.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record011_frame007_links_0000 record011_frame007_links_0064)
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0469
    Papers.RationalityTen.SharedFrameCatalogue.group0469_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
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
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xc055ed2ec96fca6753028fd426a014f1a7452f69554a323f11ba8a63e91e44efe76d3af9d40e8a72638b9bc0cbc6593159824bfc5dc2e89638b045692ae9550a9e52428794109ec4d926592548dc44621310587ec3e91ee8eb473a3851ba8db86ce33718b0c105d22d714f89d44d824f12308c444221210007d03ce1b40cd86402f016d0b2050c24811807581fc0b805602a815009004701e00e406a02400f007403801900b805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79ea9e59d398a98397696c96095593492b91f9128f08e38a689a88887d86e85f83982c81e80b7dd7cc7507137006c86b569869469068067c66962761f6126095fe5f25d15c85be5b058a57d54c54453652c5215144f14e64dc4ce4a949b4364043f53c73b839f39839238737c37536835b34e33032931c30f2ff2d42c829d28d27d26f26125024022f21f2102011f11e01c51bf1b31a719818817816a15b14b13b12f1221110f80d40c80ba0ae08607907806705805505405305204304203102201f01e01d01c } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame001_links_0000 (interval_append _ 64 128 135 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2e49714b845b92da969eafb57a2b5158cabb556aa294fca73533a9294689ef4f427113689a74cba5b52b694a49c24591fc87141a207cfbc7c83d31e78f2c7813ba9d6ce107013711b5cd906bd34c1a1ccf666a32818f8bfa5f82ee9744b8c5ba2cc9630afa5702aa95089a44a224a11848a4437214106c8284081fc0fa87b83ce1da8e947283851ba0d246682fc1758b6c5942bb1598a78510276132094447822a10387d43ce1d80e506ec3681a00c605f02da15b0a384dc2340ee070834418608c03d81e80d205a02b81580aa054021810806202200f807803a01c } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame002_links_0000 (interval_append _ 64 128 135 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x2fe97d6bde5daaea1706b2858a2bd95c8ad6563aa59508a76533a9214829f94f1a7053649a04c7257129a93b494a429206874420a0c50027f13ee1f28f6e77e3b59cd8dc86d13589a84d226813281900c6062030117f4b805ad2c8160cae856529d94b8a3e51027b93c890445d22890b88444131ff0fb47b43c51db8e9872e3871b28d5c68c3371938c045f42d81618ab853028113789884a424311a88a04302090fb87903a41c00d7066431217c0b7058c2b014b09e84c82480f2071036019c08c03d81e80d205a02b81580aa054021810806202200f807803a01c } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame003_links_0000 (interval_append _ 64 128 135 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x65f65564e64563e63160c6065f25e85e25df5cb5c85c15b75ac5a658657f56855f55655253953552f5265175104c94a849e47f47446646045744e44a43a41440f3fb3f13e93e63d03cd3c63bc3af3a938f38a37937236a36435134b34633f33332e2ec2d62ce2b62b12a529828c28527d27326825e25724b24123a23322821420d1f31e31d71c71bc1b51aa19e19418e18317717016115114713c1321271221191101081020f90f00ea0de0b90ad0a509d07e07307206305405105004f04e04304203102201f01e01d01c } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame004_links_0000 (interval_append _ 64 128 135 record014_frame004_links_0064 record014_frame004_links_0128))
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x338599ccbf64731e1874ba35c8adad6b0b4859c2bfd5daada5632a6950ca37512a7fd3d89dc4e6264d30296e4ad24b92348cb45b22bd134893440a1b10b08234071f60e9a73c38c1c24df26e935b1a94d2668332e1924bf05e72e196d0b485942b09540a7c52e28393d094a49024491d88e046322690e884c40c1fc8f807923b41c38dd86c234e19c0bec5ce2b11508a445042701318950486233112085840c1f70ef073837c1ae0cf86343001710b0054028213309184501f60e606f83601a408c03d81e80d205a02b81580aa054021810806202200f807803a01c } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame005_links_0000 (interval_append _ 64 128 135 record014_frame005_links_0064 record014_frame005_links_0128))
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
def record014_frame006_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7ac7a77a278b78677073772c7167086fb6f26d16c86c26b96a469d67966e65b65264c6436226146075fe5e65df5ad59859157c57556b56155653752c5104d54c74b14a749c49046f46645c45243843140c3fe3ec3e33d93cf3a939f39438836f36833732231c3073012f82f12e92de2d42c42b42a629827c26c25c24e24021f2181ff1f31e41da1cb1be1b61ad1a419b19318a18117516915d14e14413512812011710e1050fd0f40eb0df0cd0c80c40c008c07b07a06905a05705605505404304203102201f01e01d01c } : Fields).get c.val)
theorem record014_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 6)
      (record014.inverseMaps 6) record014_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame006_links_0000 (interval_append _ 64 128 135 record014_frame006_links_0064 record014_frame006_links_0128))
theorem record014_frame006_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 6 :=
  of_group record014 6 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record014_frame006_indices record014_frame006_graph record014_frame006_links
def record014_frame007_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0246.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0246.count (({ width := 9, code := 0x582bd5dae56eb556aad4ea34fa6d2e9548a35168741a04fe7b3b9d4e26f3599cc25f2993c9647228fc76391b8d4662b14894421d0c854260f058240a00ff7f3f1f4f97bbd9e8f277bb9d0e672389c2dd6cb59a4ce65b1d84c05e2e56eb5582a952a24f2712e954923d1a8a43a11047f3d1dcea70371a8ce6430174b6592b1509e4a2491886401d8e86a30178b85a2c13898421c0d8683218 } : Fields).get c.val)
theorem record014_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record014) (record014.maps 7)
      (record014.inverseMaps 7) record014_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame007_links_0000 (interval_append _ 64 128 135 record014_frame007_links_0064 record014_frame007_links_0128))
theorem record014_frame007_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 7 :=
  of_group record014 7 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0246
    Papers.RationalityTen.SharedFrameCatalogue.group0246_facts record014_frame007_indices record014_frame007_graph record014_frame007_links
def record014_frame008_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0240.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0240.count (({ width := 8, code := 0xd4d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0aeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8b888683807d7b79777572706e6c6a6968666462605d5b59575553514f4d4c4a484644413f3d3b3937353331302f2e2d2a2726242221201f1e1b1a181615141312 } : Fields).get c.val)
theorem record014_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0240.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record014) (record014.maps 8)
      (record014.inverseMaps 8) record014_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame008_links_0000 (interval_append _ 64 128 135 record014_frame008_links_0064 record014_frame008_links_0128))
theorem record014_frame008_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 8 :=
  of_group record014 8 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0240
    Papers.RationalityTen.SharedFrameCatalogue.group0240_facts record014_frame008_indices record014_frame008_graph record014_frame008_links
def record014_frame009_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0244.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0244.count (({ width := 8, code := 0xc0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a78767472706e6c6a68666462605e5d5c5a58565452504e4c4a48464442413f3d3b39373533312f2d2b2927262524232221201f1e1d1c1b1a1918171615141312 } : Fields).get c.val)
theorem record014_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0244.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0244.localPairCheck (smallEmbedding record014) (record014.maps 9)
      (record014.inverseMaps 9) record014_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame009_links_0000 (interval_append _ 64 128 135 record014_frame009_links_0064 record014_frame009_links_0128))
theorem record014_frame009_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 9 :=
  of_group record014 9 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0244
    Papers.RationalityTen.SharedFrameCatalogue.group0244_facts record014_frame009_indices record014_frame009_graph record014_frame009_links
def record014_frame010_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0142.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0142.count (({ width := 8, code := 0x868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0142.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0142.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0142.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0142.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0142.localPairCheck (smallEmbedding record014) (record014.maps 10)
      (record014.inverseMaps 10) record014_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame010_links_0000 (interval_append _ 64 128 135 record014_frame010_links_0064 record014_frame010_links_0128))
theorem record014_frame010_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 10 :=
  of_group record014 10 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0142
    Papers.RationalityTen.SharedFrameCatalogue.group0142_facts record014_frame010_indices record014_frame010_graph record014_frame010_links
def record014_frame011_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32e1946c9162cb11980eb675aa2cb162cb04578aacd53ea8b53b292946a9dc4e526913269804b6a4d124090e47e234517c8303fd9fa4f6e7a73c21dbceba7253891b4cc666202fc1788ba05bd2bf95acaae54228b1404950496238117c8984392000fb07b43c81ce8e285f82c715a8a0c4e6256127892848623a11a88b844e220108082c4081fd0fb07883b61c40de86d835e1a70d0866832418b0c285f82ec16f0b2056c2a814d0a304f8270131094848823811508684181f60e606f83601a408c03d81e80d205a02b81580aa054021810806202200f807803a01c } : Fields).get c.val)
theorem record014_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 11)
      (record014.inverseMaps 11) record014_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame011_links_0000 (interval_append _ 64 128 135 record014_frame011_links_0064 record014_frame011_links_0128))
theorem record014_frame011_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 11 :=
  of_group record014 11 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame011_indices record014_frame011_graph record014_frame011_links
def record014_frame012_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x69769368b68167b66863563061e61460a6005ea5e35da5d25c05b458d58757456b56255954653f53352c51950d4c94a749a47b46f45d45745444644242e3fb3f63e33d93d23c83af3a73a139a38637a35334d33933032a32130a3032fb2f42df2d328f26a25f23e23422321b21421020a2051fd1f61ee1e21dd1d41cc1c31b31ac19318b18217a17216e16816115915114c14413b12f12a12511e11911210e1091030fb0f40f00ea0e30d70c50bd0b70b108807907806705805505405305204304203102201f01e01d01c } : Fields).get c.val)
theorem record014_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 12)
      (record014.inverseMaps 12) record014_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame012_links_0000 (interval_append _ 64 128 135 record014_frame012_links_0064 record014_frame012_links_0128))
theorem record014_frame012_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 12 :=
  of_group record014 12 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record014_frame012_indices record014_frame012_graph record014_frame012_links
def record014_frame013_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6cd6c26bb6a169b68465164763462b62261c5fb5f25e95e25cc5c65a459858457c57456e54f54753e53752051a4d34ba4b249448a47d47146b45344c4344013f73e23d93d03c93a839f39639037c3763543483313293203192fa2f22ea2e42d02ca28326425a24123922c22522021921120a2011fa1f21e01d91d01c91c11ae1aa19a19318c18517e17817016615d15514d14313a13012a12512011b11410f1091010fb0f50ef0e70e10d80c60c00b90b208c07b07a06905a05705605505404304203102201f01e01d01c } : Fields).get c.val)
theorem record014_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record014) (record014.maps 13)
      (record014.inverseMaps 13) record014_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame013_links_0000 (interval_append _ 64 128 135 record014_frame013_links_0064 record014_frame013_links_0128))
theorem record014_frame013_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 13 :=
  of_group record014 13 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record014_frame013_indices record014_frame013_graph record014_frame013_links
def record014_frame014_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x11aa32c618bb16627c3185908e0e416825012003fa7e6fa1f13ce794f01dd3b4762e89cfb9b728e1dc13616a4d359db36656c9991b1d632c41792ed5c2b696aad1584af95d2b3552a8d47a8b4fc9dd3826d4be9712ca5349090d112114147e8fb1ed3cc780ee1d73a2720e01ba35c6a0d119c32660cbf96a2c2568a894b28c4f49992a24846c8890a2003e87a8f01d6398708db1a8338648c31782dc5789e12e2484687a0e01bc3005109c1342604b0821001882203e0780e81c } : Fields).get c.val)
theorem record014_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record014) (record014.maps 14)
      (record014.inverseMaps 14) record014_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame014_links_0000 (interval_append _ 64 128 135 record014_frame014_links_0064 record014_frame014_links_0128))
theorem record014_frame014_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 14 :=
  of_group record014 14 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record014_frame014_indices record014_frame014_graph record014_frame014_links
def record014_frame015_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x1f47c5f07bded7b1e5791e0771da75dd2745ce729c8715c3709bd6e9b86d9b26c5ae6ada66919764d9163d8c621866158460d825d9755c96f5b169591635815d56156551525414d52d4850d414fd3c4dd344b129495224851c4651644d1043508409003ecf83d4f33b4e4384d834cd132cc8314c02f4b82d0af2b0a82809d268942488d228862007b1e0751c06d1945c164551444810c420f0360cc320c4300ac2a0881c06c1a06418 } : Fields).get c.val)
theorem record014_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record014_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record014) (record014.maps 15)
      (record014.inverseMaps 15) record014_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record014_frame015_links_0000 (interval_append _ 64 128 135 record014_frame015_links_0064 record014_frame015_links_0128))
theorem record014_frame015_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 15 :=
  of_group record014 15 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record014_frame015_indices record014_frame015_graph record014_frame015_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (Fin.cases (record014_frame006_supported hcells) (Fin.cases (record014_frame007_supported hcells) (Fin.cases (record014_frame008_supported hcells) (Fin.cases (record014_frame009_supported hcells) (Fin.cases (record014_frame010_supported hcells) (Fin.cases (record014_frame011_supported hcells) (Fin.cases (record014_frame012_supported hcells) (Fin.cases (record014_frame013_supported hcells) (Fin.cases (record014_frame014_supported hcells) (Fin.cases (record014_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xb925c52e116e4b6a5a92bed5e8ad45632aed55aa8a53f29cd4cea4f51ca7bd3d09c44da269d32e96d4ada52927091b481a1c506881f3ef1f20f627a63cf1e58f027753af1c20e026e236b9b20d7a69834399eccd465532197f4bf05dd2e89718b745992c615f4ae055a2a39348944494230914888443121110608224011f70f7c7a43c31d68e647143791b50d406762f31710b485822b81538a4c50226f12d092046c22410807b43be1d00e106e43541970c305d82ca1500a104c824205702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame001_links_0000 (interval_append _ 64 128 141 record015_frame001_links_0064 record015_frame001_links_0128))
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4559dacd162eb065732a5d518a7753629994c0a3951028454029e14e8a6252f69634aaa53528c91a480a3b91ba8b7453203cfb67d23c91dfceda75f3a81d14e527173781a60d16673333197ccb263130e1834bfc5e02e89638b045692ae9550a9e52928a14109ec4d9265915c85e4261fb8fa47ba3c91db8ea473a38f1c08dd46da3671a80ce06443131820b985ae29c14489dc4d8260128891847423111188484021f40f387143681a70cd86403081780b685902ac143098849023005702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame002_links_0000 (interval_append _ 64 128 141 record015_frame002_links_0064 record015_frame002_links_0128))
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x414821032054077faf8df0bda7b0f55e9bca78cf05debb4760e81ce396724e3dc5b816f2dc9b535f6aec9d8b3125f6bc974ae25beb716cad358cab1552a4544a7d4ea9451ca21412784e49812ea574a89452724447c8dd18a274427d0f29e23a0728e21bb3686b4d49a533c668cb192320618be9742d6578aa9402784d0981292484808c91521c424820fd1ec398700d91a6334648c317a2e8598ab1502884e0410800fc1f01c0360680c81702c0540a0130240440800a0120200380400600800800 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame003_links_0000 (interval_append _ 64 128 141 record015_frame003_links_0064 record015_frame003_links_0128))
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
def record015_frame004_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xbfa5f5af7976aba85c22ca1628af65722b5958ea9654229d94cea4a521a7e53c69c14d9268131c95c4a6a4ed25290c482a1d10828314009fc4fce7dc3e51edcefc76b39b9b90da26b13509a44d0265032018c0c406042ff9700b5a5902c195d0aca53b297147ca204f927a12088ba451217108883440b1fb0f8079a3be1d60e7071837c1af0d3067832c18e0c105fa2cd15c0a88518279133896849a23e11688804262040fd076838e1b60d186483041760b605802a214509d84bc24c05702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record015_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record015) (record015.maps 4)
      (record015.inverseMaps 4) record015_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame004_links_0000 (interval_append _ 64 128 141 record015_frame004_links_0064 record015_frame004_links_0128))
theorem record015_frame004_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 4 :=
  of_group record015 4 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record015_frame004_indices record015_frame004_graph record015_frame004_links
def record015_frame005_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x65f65564e64563e63260c6065f25e85e25df5cb5c85c15b75ae5a858657f56855f55655253953552f5265195124c94a849e47f47446b46646045744e44a43b41440f3fb3f13e93e63d03cd3c63bc3b13ab38f38a37937236a36435134b34633f3353302ec2d62ce2b62b12a929f29228928227826b26225825124623b23422b2222172101ec1dc1d01c01b91af1a519c19118817e17416e16414b14113612c12511e11510e1060fe0f50ee0e80e005105004f04e01f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record015_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 5)
      (record015.inverseMaps 5) record015_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame005_links_0000 (interval_append _ 64 128 141 record015_frame005_links_0064 record015_frame005_links_0128))
theorem record015_frame005_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 5 :=
  of_group record015 5 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record015_frame005_indices record015_frame005_graph record015_frame005_links
def record015_frame006_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x3f07dafa9f0bde7aaefddcbaf752e99d1b9571ee31c4b826fedb5b3b5d6aed4da8341676cdd9a32b650c0d75ae559cb2161abf570ac55329f5289e9392654ba9692ba4647c8ed1c23145c8710a2073fe7e4fb1e83c0768eb9d039a6a4c918c2f05c8b796d2d0584ae9572a0530a394427c4dc9992e2564989191922c448869092043f47c8f31e03ac738e11be360688cd194318600bd1722d0588ae1542945184b0941242401f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record015_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record015) (record015.maps 6)
      (record015.inverseMaps 6) record015_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame006_links_0000 (interval_append _ 64 128 141 record015_frame006_links_0064 record015_frame006_links_0128))
theorem record015_frame006_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 6 :=
  of_group record015 6 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record015_frame006_indices record015_frame006_graph record015_frame006_links
def record015_frame007_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0899.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0899.count (({ width := 8, code := 0xaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999796949391908e8d8b8a8887868584838281807f7e7d7c7b7a797877767574737271706f6e6c6b696866656362605f5d5a585755545352514f4e4d4b4a484746444341403e3d3c3b3a393837363534333231302f2e2c2b29282725242322201f1e1d1c1b1a1914131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record015_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0899.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0899.localPairCheck (smallEmbedding record015) (record015.maps 7)
      (record015.inverseMaps 7) record015_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame007_links_0000 (interval_append _ 64 128 141 record015_frame007_links_0064 record015_frame007_links_0128))
theorem record015_frame007_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 7 :=
  of_group record015 7 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0899
    Papers.RationalityTen.SharedFrameCatalogue.group0899_facts record015_frame007_indices record015_frame007_graph record015_frame007_links
def record015_frame008_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1031.count (({ width := 10, code := 0x31fc7319c470ec1af9bdaf2bbeecba6e3b82ddb6ad5b4ac5b02b9ad2b0ab6a2a7699a5a8ea2e6e97658922438fe3c8da2f8961e84e027f5f67c5ee7ade1771d9759d0735c16e9b16a9a4685986458b621825fd645514f5053c4e5374d12e4a9264811c45d144410a419013f8f93d8ee3ace738ce1374d935cd4344cd32cc8318c12e8b62ccaf2a4a62889d2689724c8e2304a1244811c1f0781d0701a0641805c15050110400a0240801c0400c0200400 } : Fields).get c.val)
theorem record015_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record015) (record015.maps 8)
      (record015.inverseMaps 8) record015_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame008_links_0000 (interval_append _ 64 128 141 record015_frame008_links_0064 record015_frame008_links_0128))
theorem record015_frame008_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 8 :=
  of_group record015 8 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1031
    Papers.RationalityTen.SharedFrameCatalogue.group1031_facts record015_frame008_indices record015_frame008_graph record015_frame008_links
def record015_frame009_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0921.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0921.count (({ width := 8, code := 0xaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999796949391908e8d8b8a8887868584838281807f7e7d7c7b7a797877767574737271706f6e6c6b696866656362605f5d5a585755545352514f4e4d4b4a484746444341403e3d3c3b3a393837363534333231302f2e2c2b29282725242322201f1e1d1c1b1a1914131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record015_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0921.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0921.localPairCheck (smallEmbedding record015) (record015.maps 9)
      (record015.inverseMaps 9) record015_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame009_links_0000 (interval_append _ 64 128 141 record015_frame009_links_0064 record015_frame009_links_0128))
theorem record015_frame009_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 9 :=
  of_group record015 9 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0921
    Papers.RationalityTen.SharedFrameCatalogue.group0921_facts record015_frame009_indices record015_frame009_graph record015_frame009_links
def record015_frame010_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0909.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0909.count (({ width := 9, code := 0x1a5d0e7f3b9bcd65f2990c76331588c36130581bf5eef376ba5cee370b75b6d76ab457ab156a8d3e9d4ca350a7d3a9c4ca5f2a93c96451f8e46a2f1689c3a19088341204ff7ebedf2f77abadcae36f371b6d76a34d9eca6330d7ebc5cad564ae55aa94ca14ea692c9548a35168943209007e3e9e4ec72379b4d26631984bc5b2c158aa351a0cc641b0d06430160a85026110803c1c0a048200e04018080200 } : Fields).get c.val)
theorem record015_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record015) (record015.maps 10)
      (record015.inverseMaps 10) record015_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame010_links_0000 (interval_append _ 64 128 141 record015_frame010_links_0064 record015_frame010_links_0128))
theorem record015_frame010_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 10 :=
  of_group record015 10 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0909
    Papers.RationalityTen.SharedFrameCatalogue.group0909_facts record015_frame010_indices record015_frame010_graph record015_frame010_links
def record015_frame011_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79ea9e59d498a98397696c96095593492b91f9128f48e78a689a88887d86e85f83982c81e80b7e27d17507137006c86b56a269869469068067c66a62761f6126095fe5f25d15c85be5b058f58254c54453652c5215144f14e64dc4ce4ae4a04364043f53c73b83a839c39538837d37936b35e35034332d31e3113032f32d72cb29528527426625a24823822821a2081f91e91db1cd1b91ad19f19018317216415614613612a11c10b0fe05505405305201f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record015_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 11)
      (record015.inverseMaps 11) record015_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame011_links_0000 (interval_append _ 64 128 141 record015_frame011_links_0064 record015_frame011_links_0128))
theorem record015_frame011_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 11 :=
  of_group record015 11 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record015_frame011_indices record015_frame011_graph record015_frame011_links
def record015_frame012_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x4f09df3ba744e69bd326634c19792e65b4a89452724bc8e9111be364688c717e2e4488790ce14c1a826f21d53a270edf9b9b6b6d4da5b235f6acd019db35662cb194b21638c5587b045feb9570ade5b6b5d6aac9580ae15729f5349611f235438851062034007e8fb9f53e27b0f49e63be758e61c33786b0d29882fa5dcb79692c2574aa14e28c4fc9d13325a4788990a2083fc7c0f31d63946e8d41963045c04909011c2301f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record015_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record015) (record015.maps 12)
      (record015.inverseMaps 12) record015_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame012_links_0000 (interval_append _ 64 128 141 record015_frame012_links_0064 record015_frame012_links_0128))
theorem record015_frame012_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 12 :=
  of_group record015 12 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record015_frame012_indices record015_frame012_graph record015_frame012_links
def record015_frame013_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0509.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0509.count (({ width := 8, code := 0xf7f6f5f4f3f0ebeae9e8e7e6e5e4e3e2dfded9d8d7d6d5d4d3d2d1d0cecdc6c3c2c1bfbdbbbab9b8b7b4afaeadacabaaa9a8a7a6a3a29d9c9b9a99989796959492918a87868583817f7e7d7c7b7a797877767472706e6b696563615f5e5c5a595857565553514e4c4a4847454342413f3d3c3b3a2a2928271c1b1a1917161514131211100a0908070403020100 } : Fields).get c.val)
theorem record015_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0509.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0509.localPairCheck (smallEmbedding record015) (record015.maps 13)
      (record015.inverseMaps 13) record015_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame013_links_0000 (interval_append _ 64 128 141 record015_frame013_links_0064 record015_frame013_links_0128))
theorem record015_frame013_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 13 :=
  of_group record015 13 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0509
    Papers.RationalityTen.SharedFrameCatalogue.group0509_facts record015_frame013_indices record015_frame013_graph record015_frame013_links
def record015_frame014_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0500.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0500.count (({ width := 8, code := 0x8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record015_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0500.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0500.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0500.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0500.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0500.localPairCheck (smallEmbedding record015) (record015.maps 14)
      (record015.inverseMaps 14) record015_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame014_links_0000 (interval_append _ 64 128 141 record015_frame014_links_0064 record015_frame014_links_0128))
theorem record015_frame014_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 14 :=
  of_group record015 14 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0500
    Papers.RationalityTen.SharedFrameCatalogue.group0500_facts record015_frame014_indices record015_frame014_graph record015_frame014_links
def record015_frame015_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xce166732fd91cc7861eae8d722b6b5ac2d21670aff576ab6958ca9f545a8dd44a9ff4f627713989934c0a5b92b493348fa32d16c8af44d224d118881436216104680e3ed9d34e787183849be4dd26b63529a4cd0666132717e0bce5c32da1690b285612a814f8a5c50c27c929492048923b11c08d445b22210b08304031f40f447743a61bf8da06aa33f1950c085dc2a814c0a244f226b12d092c47822d10e08344001f20f2071436a1a60cb06202ee1680ac852827212a08e843c20205702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record015_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 15)
      (record015.inverseMaps 15) record015_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame015_links_0000 (interval_append _ 64 128 141 record015_frame015_links_0064 record015_frame015_links_0128))
theorem record015_frame015_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 15 :=
  of_group record015 15 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record015_frame015_indices record015_frame015_graph record015_frame015_links
def record015_frame016_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x75174b74773a7367236e86e26cb6c16b96b069668a68067766765662d6276116086005f65dc5d35cb5bf5ac59b55954653f52a52351c51750e5074f44eb4d648f48947046745c45543942f4234184053f43c23bc3a439d39438b36e36335834e3383272e42d12ca2b72b12ab2a229728e28727d27026325924c23c23022221820a1f31e81c21bb1b41ad1a81a019618f18617b16f16916015814213b13412d12812011610d1070fb0ef0e70e20d805705605505401f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record015_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 16)
      (record015.inverseMaps 16) record015_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame016_links_0000 (interval_append _ 64 128 141 record015_frame016_links_0064 record015_frame016_links_0128))
theorem record015_frame016_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 16 :=
  of_group record015 16 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record015_frame016_indices record015_frame016_graph record015_frame016_links
def record015_frame017_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x63f63d63b62a6266145e25db5d25cc5c85c25aa59c59258957356854553f53452d5265205084fa4f04e54d14c848c47847246045945344e44944442f4284113db3d23c43bd3b83b339938d37e37535f35633032931d3143093042ea2de2cf2c62b02a726d25a25524423d23723122a21f2172112061fe1f81f31e81da1d01c61be1ab1a318617b17517116e16716215d15815314914013a13412411911110c1071010fd0fa0f60f10e70de0d60d205505405305201f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record015_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record015) (record015.maps 17)
      (record015.inverseMaps 17) record015_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame017_links_0000 (interval_append _ 64 128 141 record015_frame017_links_0064 record015_frame017_links_0128))
theorem record015_frame017_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 17 :=
  of_group record015 17 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record015_frame017_indices record015_frame017_graph record015_frame017_links
def record015_frame018_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0934.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0934.count (({ width := 9, code := 0x147a35168943a0cf277399c4de6d3398cbe5b2993c823f1d8e46e35178ac4e230d85bf9f2f7793c1dced763add4e97337dbcdc6db69b2d76ab4da2ce663198ac36130580be5e2e970b559a9d44a04e26930964a249229047235188b44a1d08823f9ecf070371b0d46933994c8633097cba5b2c950a4502713496492411c8a43208fc7a2b150a4501c0d86832170b054281309044200a048200e04018080200 } : Fields).get c.val)
theorem record015_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0934.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record015) (record015.maps 18)
      (record015.inverseMaps 18) record015_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame018_links_0000 (interval_append _ 64 128 141 record015_frame018_links_0064 record015_frame018_links_0128))
theorem record015_frame018_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 18 :=
  of_group record015 18 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0934
    Papers.RationalityTen.SharedFrameCatalogue.group0934_facts record015_frame018_indices record015_frame018_graph record015_frame018_links
def record015_frame019_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x48b91121a3e47a8db12a2243a8690c215c1d82f04e06c047faf9df0bd579ef2de2bb8766ec1d53a1734dc9b135b690d099e339662ca58e31760cb6d6baca588afd5e2aa54aa814d28d50e9ad33a574a292922a344628b513a1d42e7b0ee1d63866f8dc1b2356694cf99b326630c31802f25c4b59662be558a913f2744d09792b24e4889011c22a43c859062043dc790ed1d03906f0d81a833c650c51842fc5d8530a41442801f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record015_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record015) (record015.maps 19)
      (record015.inverseMaps 19) record015_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame019_links_0000 (interval_append _ 64 128 141 record015_frame019_links_0064 record015_frame019_links_0128))
theorem record015_frame019_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 19 :=
  of_group record015 19 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record015_frame019_indices record015_frame019_graph record015_frame019_links
def record015_frame020_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0600.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0600.count (({ width := 11, code := 0x3da7b2f61e8bcf794eeddbbb3762eb1d3b99726e31c13786e4d81aeb5a6acd49a6b3f672ccd96b22636bb16dad7592b15602bc574ae158aad546a3d44a855029f13b26b4c697d2b24c48c8c91722a44e8850ea0f41680cfe1f13da710da9b0346680ce19832a640c698a30e608be9782e45b4b395e2ac530a29322524949011e230444869092043f07b8f21d837c6d0d119831c618c11782e05a0ac14c2844d04f09c1342601f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record015_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record015) (record015.maps 20)
      (record015.inverseMaps 20) record015_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame020_links_0000 (interval_append _ 64 128 141 record015_frame020_links_0064 record015_frame020_links_0128))
theorem record015_frame020_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 20 :=
  of_group record015 20 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0600
    Papers.RationalityTen.SharedFrameCatalogue.group0600_facts record015_frame020_indices record015_frame020_graph record015_frame020_links
def record015_frame021_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcb8651b2458b2c466052d9d6a8b2c58b2c115e2ab354faa2d4eca4f51d27713949a44c9a6012da93449024391f88d6461a0c0ff67e93db9e9cf2a7843b79d74e4a71236b18ccc405f82f11740b7a57f2b5955ca8451b28312a092c47022f91308724001f60f687903a21c78bf058e2b514189cc4c2255127091447c23911808a444421b10788183fe1f80f8878c3b81c10dd06cc3581a60cf065c32218a0c105ec2ea16e0b385602a214a0a184f426a12e094048423211208604141fc05702b01540a801f00f007403801a00c806002e01500a004402000a004802000e0040018008002000 } : Fields).get c.val)
theorem record015_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 21)
      (record015.inverseMaps 21) record015_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame021_links_0000 (interval_append _ 64 128 141 record015_frame021_links_0064 record015_frame021_links_0128))
theorem record015_frame021_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 21 :=
  of_group record015 21 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame021_indices record015_frame021_graph record015_frame021_links
def record015_frame022_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x67166b66565764f6386035fc5f05e75e25dd5cd5c35ba5b159c59156655e54f54653f5395225155094fe4e74da49247546e45144843d43542f42941b4123fe3c73be3b43ad3a63a139138737d37235c35332a32131230a3032fd2e62d92cb2be2a629b24f2392322152092001f91f11ea1e31dd1d61cf1cb1c81c11b91b21ac1a419418c17817116a16415d15414e14714013d13913513012911d11911310c1070ff0f80f30ed0ea0e50e00db0d505605505405301f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record015_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 22)
      (record015.inverseMaps 22) record015_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame022_links_0000 (interval_append _ 64 128 141 record015_frame022_links_0064 record015_frame022_links_0128))
theorem record015_frame022_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 22 :=
  of_group record015 22 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record015_frame022_indices record015_frame022_graph record015_frame022_links
def record015_frame023_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0938.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0938.count (({ width := 9, code := 0x184c1e0b037fbddcee570b7dbadb6ab459ac960af55ead53a95429f48a2d067d389ac9643208dc662f158a44e2510864120701803fdfcfb7cbddeaf177ba1cee471b85c0d96b3499ec9632d964b1562a950a65228942a04f275389b4d25d289247a311282401f8f87b3c9dcec75399c4de6d35994c6612f978b85a2c960ac532893c9a32188c05e1c0d86832170b054281309044200a048200e04018080200 } : Fields).get c.val)
theorem record015_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 23)
      (record015.inverseMaps 23) record015_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame023_links_0000 (interval_append _ 64 128 141 record015_frame023_links_0064 record015_frame023_links_0128))
theorem record015_frame023_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 23 :=
  of_group record015 23 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0938
    Papers.RationalityTen.SharedFrameCatalogue.group0938_facts record015_frame023_indices record015_frame023_graph record015_frame023_links
def record015_frame024_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6cd6c26bb6a169b68565164763462b62261c5fb5f25e95e25ce5c85a459858457c57456e54f54753e53752251c4d34ba4b249448a48147d47146b45344c4354013f73e23d93d03c93a839f39639037e3783543483313293203192fa2f22ea2e42d22cc28326425a24123923122b22421b21520f2041fb1f41ec1de1d31ca1c31bb1af1ab19719018918217d17416c16415b15114914113813112812211d11811310b1050ff0f90f10eb0e50df0d905705605505401f01e01d01c01a01901801701501401101000a009008007004003002001000 } : Fields).get c.val)
theorem record015_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record015) (record015.maps 24)
      (record015.inverseMaps 24) record015_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame024_links_0000 (interval_append _ 64 128 141 record015_frame024_links_0064 record015_frame024_links_0128))
theorem record015_frame024_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 24 :=
  of_group record015 24 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record015_frame024_indices record015_frame024_graph record015_frame024_links
def record015_frame025_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1030.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1030.count (({ width := 9, code := 0x1b1d76b34ba3cee57258fc662b1183c05faf978bb5bed767b1d86bf59aad4ea34da5d0677389a4c6612e95ca645208d44a1f0c84c1e0b007ebedf2f579bb1d0e470379b8d6693419cca642f970b558ab95aac5529946a24f26d34994ba4d208f47231168843a1104813f1f0f6793b9d4e872389b8d86933998c66130178b85a2c95cac34198c8621f0f074381a0c8602e150a044200a048200e04018080200 } : Fields).get c.val)
theorem record015_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1030.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record015) (record015.maps 25) (record015.inverseMaps 25) record015_frame025_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record015) (record015.maps 25) (record015.inverseMaps 25) record015_frame025_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record015) (record015.maps 25) (record015.inverseMaps 25) record015_frame025_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1030.localPairCheck (smallEmbedding record015) (record015.maps 25)
      (record015.inverseMaps 25) record015_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame025_links_0000 (interval_append _ 64 128 141 record015_frame025_links_0064 record015_frame025_links_0128))
theorem record015_frame025_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 25 :=
  of_group record015 25 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1030
    Papers.RationalityTen.SharedFrameCatalogue.group1030_facts record015_frame025_indices record015_frame025_graph record015_frame025_links
def record015_frame026_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0920.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0920.count (({ width := 8, code := 0x8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record015_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0920.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record015) (record015.maps 26) (record015.inverseMaps 26) record015_frame026_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record015) (record015.maps 26) (record015.inverseMaps 26) record015_frame026_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record015) (record015.maps 26) (record015.inverseMaps 26) record015_frame026_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0920.localPairCheck (smallEmbedding record015) (record015.maps 26)
      (record015.inverseMaps 26) record015_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame026_links_0000 (interval_append _ 64 128 141 record015_frame026_links_0064 record015_frame026_links_0128))
theorem record015_frame026_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 26 :=
  of_group record015 26 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0920
    Papers.RationalityTen.SharedFrameCatalogue.group0920_facts record015_frame026_indices record015_frame026_graph record015_frame026_links
def record015_frame027_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0908.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0908.count (({ width := 9, code := 0x1218fc7a3b1c8dc662f158a44e25118843e1d0d85c260f058240e0501803fdfcfd7dbd1deed74b9dcce471385c0df6f371b4d86bb59aad469b49a2d06733194c863b198ac461b0982c05f2dd64b0562a952a65228d429e4e26930964a249208e4622d1285411fcf87b3b9d0e470369a8d06632984bc5b2c15ca6502713092462210882291409c4c1b0d06430160a85026110803c1c0a048200e04018080200 } : Fields).get c.val)
theorem record015_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0908.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record015) (record015.maps 27) (record015.inverseMaps 27) record015_frame027_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record015) (record015.maps 27) (record015.inverseMaps 27) record015_frame027_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record015) (record015.maps 27) (record015.inverseMaps 27) record015_frame027_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0908.localPairCheck (smallEmbedding record015) (record015.maps 27)
      (record015.inverseMaps 27) record015_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame027_links_0000 (interval_append _ 64 128 141 record015_frame027_links_0064 record015_frame027_links_0128))
theorem record015_frame027_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 27 :=
  of_group record015 27 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0908
    Papers.RationalityTen.SharedFrameCatalogue.group0908_facts record015_frame027_indices record015_frame027_graph record015_frame027_links
def record015_frame028_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x4b595f2b251c9f9331e639c6b8c91862cc4a8830f61a429847036023fc7ecfcdf73e17b2f4de5bbc76ae1dbab6d6acd35a3343678ce19832d64ec1981af65e2ba172ad159ab19622b5566a654a2885069f13b2634be9652ba48488854ff9f63c676cea1d139a71ce01ba3646b0d39a132c63cc49832fa5c4b515c2ac540a59472824e49a12d24a47c8c91221a41c810fc1ec3c4748e11b8358668c71822ec5b04f09c1342601f03c0740e01a0320600b8150280440800a0120200380400600800800 } : Fields).get c.val)
theorem record015_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record015) (record015.maps 28) (record015.inverseMaps 28) record015_frame028_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record015) (record015.maps 28) (record015.inverseMaps 28) record015_frame028_indices (Fin.ofNat record015.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record015_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record015) (record015.maps 28) (record015.inverseMaps 28) record015_frame028_indices (Fin.ofNat record015.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record015_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record015) (record015.maps 28)
      (record015.inverseMaps 28) record015_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record015_frame028_links_0000 (interval_append _ 64 128 141 record015_frame028_links_0064 record015_frame028_links_0128))
theorem record015_frame028_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 28 :=
  of_group record015 28 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record015_frame028_indices record015_frame028_graph record015_frame028_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (Fin.cases (record015_frame004_supported hcells) (Fin.cases (record015_frame005_supported hcells) (Fin.cases (record015_frame006_supported hcells) (Fin.cases (record015_frame007_supported hcells) (Fin.cases (record015_frame008_supported hcells) (Fin.cases (record015_frame009_supported hcells) (Fin.cases (record015_frame010_supported hcells) (Fin.cases (record015_frame011_supported hcells) (Fin.cases (record015_frame012_supported hcells) (Fin.cases (record015_frame013_supported hcells) (Fin.cases (record015_frame014_supported hcells) (Fin.cases (record015_frame015_supported hcells) (Fin.cases (record015_frame016_supported hcells) (Fin.cases (record015_frame017_supported hcells) (Fin.cases (record015_frame018_supported hcells) (Fin.cases (record015_frame019_supported hcells) (Fin.cases (record015_frame020_supported hcells) (Fin.cases (record015_frame021_supported hcells) (Fin.cases (record015_frame022_supported hcells) (Fin.cases (record015_frame023_supported hcells) (Fin.cases (record015_frame024_supported hcells) (Fin.cases (record015_frame025_supported hcells) (Fin.cases (record015_frame026_supported hcells) (Fin.cases (record015_frame027_supported hcells) (Fin.cases (record015_frame028_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))
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
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5d6b15602974e09a525a4948b90f20a3ec568610a611c1c81500def3d87a6f3de6bc976cec9cab9170ad6daab4b682bf97d2ef5d8b896eac757aab53fa7a4e09ad2723744686909a063fe7e4f81ec3c6720dd1b23105f4bc16e2b84cc9411f230430839011f83e0788ec1ce384630c01762d8588820d21582a84f09c0e41c02f05a0a8120230420740e01902e0500780e0160200380400600800800 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcdf60db0056c0a7d53327c13d09c64da26a532e92c45a228112287d42ca118fba7c73d89e98f3c7963b69da0e3c7123789a5cd0c67a33497f0bf05d92e89708b745962bd1594a0c4fb274137495c48423011448844192088fc47be3d51e18e2c6d636217b0b845aa2c0152892446a22310807ac3be1ce0e106e43501970c305d824210e08003d01ce09403801700b605502a00e407002f01680a8048023010807403801900b805001e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79dd9d799699297f93392a91e9118a689a88887d86e85f7f77927827717627387246c76b46a269869469067466d63362f6195d05c75bd5af54c54453652c5215144bd46f4624544464224123c63b73a839c39538837d37936b35e35034331f3123042f42e72a02942842732652091fa1e81da1cd1b91ad19f1901831721641561460fe0f20e70db0ce06f06e05a05905305203903802402301d01c01a01901801701501400f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2e49714b845b2ad81612b00571aa254faa7253327bd3d09c44da269d32e92c459228111e87d42e2118fba7c73d89e98f3c7963b69da0e3c7123789a5cd0c67a33497f4bf05dd2e89718b7456528513ec9d84dd26092b88c045122110c484441820890047dc3df1e90f0c73438b1bd0dac6c43061790b845a22c012d892446a22310807b43be1d00e106e43541970c305d824211008003d01ce07103801700b605502a00e4070024011807403801a00c806002e01500a003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x130a5fcbd9712de4d4999291b634c658bb0e21bc2d8510960fbee770ec5d73a7734e4db53616bad61aab53696d2595328644c097eaf95e6b35662c457cae95a28e4c49692ba5449291112a1e43685909a0f418820fe1f73e47a0eb1d0396704dd99f32c640c61842a65289f93626649c9011c22c440849011f43c45d0b115027c4b0610c01382684708c0dc1b0240460740e01a0320600b81502803c0700c0160200380400600800800 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x536974aa4d228f46a2d128742a0ce26f3499cca63309348e411d8cc5a1f0c8441a09038140600ff7f3f5f8fb7d3c5e0ed763add4e96fb71b2d66933d90c560af572b4582b956a953a9546a14fa753694482351487401f8f8793b1c4dc6b34198c6602e96caa5227930923c1d8d0662d160a04e200f86430160a85026110803c1c0c058200e04018080200 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
def record018_frame005_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32e1946c9161ab07971ab7a59faac953ca8a53aa7713949a44c9a6012da8e743c21990a884440e2028f6c7a63ca9e10ede75d3809ba8cb264630595f8ad45562a092a092c47022f91308723b31a20cc86403101740b58504272130895449c24511f08e4460229111086c40e2000fc87c83d81c90e006e43641ab0c185f02e816d0b385602a214a0a184f426a12e09404841fc0f607783a41c407103801700b605502a00e4070024011807403801a00c806002e01500a003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record018_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record018_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 5)
      (record018.inverseMaps 5) record018_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record018_frame005_links_0000 record018_frame005_links_0064)
theorem record018_frame005_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 5 :=
  of_group record018 5 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame005_indices record018_frame005_graph record018_frame005_links
def record018_frame006_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x20881a05812037f1fb7e9f47cdf27c5e5791df775db765d06e9b66c9ae6a5a5661936358a62187619855f97d5e9725c16e5b15855d53549515414a4f1384d1304a9254651543d0a419013f4fa3d8f33c0ed3a0e5388df370d032cc730cbf2b8ab2a4a4278962488e228872107f1e47619c621785a158400fc360d42f0b82a0a42007c19060160541404c110400f0380c02c0801c0400c0200400 } : Fields).get c.val)
theorem record018_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record018_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record018) (record018.maps 6)
      (record018.inverseMaps 6) record018_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record018_frame006_links_0000 record018_frame006_links_0064)
theorem record018_frame006_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 6 :=
  of_group record018 6 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record018_frame006_indices record018_frame006_graph record018_frame006_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (Fin.cases (record018_frame005_supported hcells) (Fin.cases (record018_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x10820ec1c80d015fbbf57d4f95ee3d0780ef5dabb2746e6dc43786c6d759730c5eab91652c956eacd53aa052aa2d3d2774e49c133a614a69211da374247dcf21d539c724e11b13606acc998e3085f8bc9742e0598ae95429650c9f92924e468881041fe3ec7a0ee1d03846e0cd1983045d8b1158250460871041dc3a8740e01b4310600be1582885009a1302584a08c10c1a8320620a01182203e0780e81c } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3381994cb85eeaf296ceb54593ac1153ea71511a8413b89ca4cfa6012408f745622690607e93db9e10d526963199880be65d02b594f49de4dc25412588d644c1f60f0c6f036617e0ad4506256127892848622f116889c4081fc0f8079c3be1d90e8871037a1b60d7869c34218e0c585f82ec16b0b2056c2a814d0a304f8270125091045421a10207d83981be0d8069024811a08c04301f40de06a03481800b605a02b81580aa054027011406e03201880a004602200f807803a01c } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x110e1841c7fcfe9f4be77b4f3ddabb2746e6dc43786a0d159f337646c557eaed5d0b91612bc54ca8d49a8a4e49c133a614a69211722543e869049fe3d2778ed1d439a70cde1ad34e63cc596b2c455ca71472644b48e9082043dc780ea1c837c6c8ca17c2e4570a713e260480700da18c308560a212c250460860dc198280460740e01a0320600b8150260400700c0160200380400600800800 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0270.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0270.count (({ width := 9, code := 0x592b554a6d3291479ecee73389acce572891c863f1d8dc62271087c3a0f0681401f0f579bc9deec73389badb6cb5da8d16732d92c55fadd62a7522652c8d44a1906803d9e0e86e3599cc8612f170b253279308e45210fc78361a8cc5e2b148a04e261288c421d0c8602e150a04c2410078381a0c058200e04018080200 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0270
    Papers.RationalityTen.SharedFrameCatalogue.group0270_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0127.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0127.count (({ width := 9, code := 0x68b439bc56270983bf5f2e973b85bad568ae56ab156aa53e9748a3512673296cb24f258ec72331789c460b0380bfdfaf87a3c5deea72371acc862ae56ea44fa71329648a3112813f9ecf075391c0d86430178b056299409a42208f87835198c4602c158a04c1f0e86c34180b8582a13088401c0c058200e04018080200 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0127
    Papers.RationalityTen.SharedFrameCatalogue.group0127_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3869a90cb85c6ade964cb1554529c13b89ca4cfa6012408f743c21990a884440e1fe8f8a7a63ca9e10cb26462f91784aac53c25412588d644c1f60f0c6883321900c405d02c614889c84c2255127091447c22a11107fc3f21c90e006e43641ab0cc064030616d0b385602a214a0a184f426a12108904301fc0f607783a41c408603e81c40d806002d81540a804e02280e4068028011807403801a00c806002e015009804001c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x1642b7d49a1d42a7acf19992ee4a48e9031ea2fc4b8450620ac0b7f8fc9ecbc7780eedbfb7c6bcd699a32c608c0176ae3590aed4828a5049fd35a5b4888dd1922a440851059f13d4718df18b3065e8b916a2b053c9e921234448851041fc3e0798e31ac344620bf1722d05687b0ea1a83305a0aa13c270490860e01a0280460740e01a0320600b8150260400700c0160200380400600800800 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame005_links_0000 record020_frame005_links_0064)
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
def record020_frame006_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0126.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0126.count (({ width := 9, code := 0x3a9d2e870b81bcdd6d361aed66a34da0cf66b3196ca64b1d8cc461b0976ba5c2dd68b258ac15cad552a54ea652a9146a1502793a9a4aa3912803f1d8e86c3499cca6330174b6562a148a04e2612c9043208fc76391b8d4662d160a44e2511888421f0f06c32170a85026110803c1c0c058281208038180a04018080200 } : Fields).get c.val)
theorem record020_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0126.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0126.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0126.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0126.localPairCheck (smallEmbedding record020) (record020.maps 6)
      (record020.inverseMaps 6) record020_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame006_links_0000 record020_frame006_links_0064)
theorem record020_frame006_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 6 :=
  of_group record020 6 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0126
    Papers.RationalityTen.SharedFrameCatalogue.group0126_facts record020_frame006_indices record020_frame006_graph record020_frame006_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (Fin.cases (record020_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x5dabab6ded758eb0758a9d52ea093d66346b8b10e61341c7defa9ebbd178eee9ceb8d6c4d61a6340648c59662b45229e93b2534888fd0fa1a41c7f8fc1ec3bc74ce49be354664c597b2e4590a79442764c08c9091f83b4728d814c23c438820fe1f8318560a6144280490860f81a83206209c1182203e0780e81c0340640a81001a0280400700800800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6ce69866d6275ea5bb5b459053952e5094ea4d64a949b48b48545f45943541540d3db3c53a73a338337e36c35632f32632231d30c2fd2e32de2d62cd2bd2a72a129c29027a27426124b22321620b1fb1ef1e81cd1c21be1a419818a18317b16c14e13c13711610b0f60e70cc0c40ae07907105a05805405304604504203c03b03902402201e01d01901701000f00d00b009008004003002001000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xeef717b5c1ad2d656af3549a88d21689b4119f8b9f5ca2d9d688af0564aa71466a284fda76130895d49823991c48d846a23311868b745822a514689b44a222cea073838d9bf0d4267f32617ecbc65c62d39530a544f726112e09684ab253128093049124511ec8ee47123490cc8383ef1e08d6465c2a414b0a144ee26b12b08f045a20b10007c83821b30d106503101730ac852825011d08783e41e20e9071036c1a807603a01c40d206703281880b403d01d80d006202e016009404400d0050024010007002000c004001 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd4a67cb269926c8d64331b98a8c185ff2fa57a0afa57aab45570a8153529313dc9e94e126952ba93a48c22ad14e88844221c90b48374112030ffa7e13e59eb0e127003721b28d0666632097f8bee5df2e41620ad854528813d09e44d626993389684a524b91b08c845521e90688243f31eb8e346da2ef1700b3857e2b81518a044de24611b08903d21dd0e607003721a50c305d829c14209904542060f2072835818e07603a01c40d206703281880b403d01d80d006202e016009404400d0050024010007002000c004001 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x543a5943685507a0b3f67bcdf9b132a634788e91a22fc4386d0a2054067f2fc5ed3cc776e75ce391720e25beb766ded9db0b5769ed1583b025f0ba9652c2564a6d48a894fa9712aa4346289912a1842e841032003f0794f21dd3a6728e19b5352630bf95a2a853ca514727e4d09691d232448829001f43d0788e81b8358630c11762d0578a71442784d06b0d219c3005e0b81642903a0720cc1802d0560941100d0140240400700800c01001 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x550a5f43e85d09a0f4027c4e69bd34e6748e91720e3e4698c115a1e43885508201bf67cef01df3b4764eb5d3b9e72ee45c4b806f0db599b2d640c45792ea5acb055e2b3552a4d472834d89812fa564a893d2323e46c8a112a1e428829031f93d0724dd990310604bc9752e0584ad1482804e090119222428820fc1d83906a8cd18c2e0590ac1502844c86a0d219c3005e0b81642883906e0c01682b0540901080d0140240400700800c01001 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
def record023_frame005_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x5d7b79692d0d9fb39656c5d78ae9592afd05a053de764d39872c64948f9051e2304528830720dc1181f015fdbf57daf9df03d4794efdbcb736ccd599c32e638c197f2f45c8b195e2ab528a1942a794ee9c93425e4a890d2023a46285d071ff3d8720dd1822f25c4b49652bc540a2933256488881092063f07c0f21d438c6a8d11963045d8b21562985086e0da1a8318610be1702a03b0740d01882e0580941100d0140240400700800c01001 } : Fields).get c.val)
theorem record023_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record023_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record023) (record023.maps 5)
      (record023.inverseMaps 5) record023_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record023_frame005_links_0000 record023_frame005_links_0064)
theorem record023_frame005_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 5 :=
  of_group record023 5 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record023_frame005_indices record023_frame005_graph record023_frame005_links
def record023_frame006_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x8738387fe7f87f37f07e57d27b17a678f7877016fb6f16e86c86b469f66f66865664561c6055ea5ae5ab59b59858857b57056555a5525425355264b54ac49b4854534424223fb3f13e33d03ab3a338c36c35535434233e33632731b30d2f82f32e92dc2c22ba2a929225d2492041f91ef1e41dd1d21c41ba1a019818c16d16215814f14713a12611a1050fd0f50e50dd0d10c80c00b807207106e06606406205f05703c03a03303002d02c02502200d00a009008007004003002001 } : Fields).get c.val)
theorem record023_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record023) (record023.maps 6) (record023.inverseMaps 6) record023_frame006_indices (Fin.ofNat record023.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record023_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record023) (record023.maps 6)
      (record023.inverseMaps 6) record023_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record023_frame006_links_0000 record023_frame006_links_0064)
theorem record023_frame006_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 6 :=
  of_group record023 6 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record023_frame006_indices record023_frame006_graph record023_frame006_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (Fin.cases (record023_frame005_supported hcells) (Fin.cases (record023_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x67cb2358dcc545f4abf15e8ad655ea9f94ce9f04f3a71935295749a240517289643921a906e8223f09f2cf587a63839c04dbe6c534399a8ca460f30197f0bee5d92e11620ad85572a2940c9ca4d325f929492e487232115487a4192088fc47aa38a1b50cf45e22e21680b045702a514089bc49023611207ac39c1b90d4066030c1760a104c82260f2072835818e06903301900ba05a01f00f007203101780b805a02c015009404401900b804001a00a004802000e005002000c004001 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032
