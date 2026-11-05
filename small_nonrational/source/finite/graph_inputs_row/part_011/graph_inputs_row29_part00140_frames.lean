module
prelude
public import GraphInputsRow29Part00140Data
public import RawFrameSupport
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36dd9c4ccb63f2fd1792b6756f2acd516a25508a7712b2934487230515889943221090607f93f39edcf4e7943a51b00d2a6332d515fcaae4f126e92a084a4001ed0e346f03651980c385f82c51598a0c4e626012288c444621610788183f01e50ef075839e1c10dd86cc35a1a60c786203041750b705982b01520a5051027a12f08c843020a0db04781b00c005f02e81680b005702b0150068028013809404402000f807803801a00c004c024011008003401600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30e1764b9c5bfad05650afb553aa294e6a22507a7bd31c96d4a524051d28d344f21ed0e283240e9f78f907b03c81d38e707083599a60cf663030f97f4b625992be9514a6a52727c936c9a44a024911848a444120c0fbc7a63bd1d68e646f235219e8ca062c2f31718b485842b813f89b44b4236112083c3da1e00e8070c3721980b285082640d804781b00c005f02e81680b005702b0150068028013809404402000f807803801a00c004c024011008003401600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6f36a869c68766164e6355fa5ea5da5ad5a058d5545465335105044f74df4ce4c94a549847b46f46344d4264173fb3c03af3a137036635331a30a2fb2d62c72be2a229428f26825d23e2342292122001f11e51e11d71c61b61af1a719f18f18817e17717015d15514e14213913112712211b1161101080f20e80e10ba08b06a05e05d05b05805605505405203402802702502202001f01e01c01a01801301201101000d00b00a009007005004003002001000 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7a679b78677b75f7586f96896496405be59158357656854d54553e52952251c5024e54a646e45b43742e4223e43dc3a339236d35634d31a30c3062fe2f02df2d82d02c92c42b62b02ab28f24722420c2041dd1d31c11bc1b619718515f15814413312e11710c0e60d80cd0c40c108d06f06c06b05f05d05b05805505403e03703403302d02702502302102001d01c01301201000f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce666631f986aba054ea8894249a34bea4cd2168fa457a2610ee80d3fc1fa0f687a63ca9d28e0266c2b493b89bc46f2248ffc7ae3c61bd8d906862d91620ad0500272130891446222310b081c4021f90f987b03aa1ce0e086ec3301890b6859c2c01570a204d825e12708d042c1fc0f7074038811e06f03601ac0ca05f02e816c0b005502a00dc068033016809c04a023010007403801a00c004c024010007803801600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3931c76da2684b2e1966ca264eb23d910c8263d30056bead65672b21580ab9555aa8953a99f4b8a59125a91848523b117c8b143d21950ae84d42220f906c82f3d89c1ccec66f3349984cb464c32198fcae654c2a19460a0e4fc27312fc96c48b23d11bc8ce46022e11588a234f1980c7c5fc2dd1570a3c4fc25d11e08a844621c10a86dc2f81690ab84c01e60d2050825c0f206f02e816c0b405802b0154082037012808c04402000f0074026010007803801a00b00500240100050018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1b02cc265331a587eb1c52ea9054089da4b4254d296945498248923690d47fa3bd1c28da40e9e58ebe6fc35d9abcd0866f3221828ac653a29593d09c04d1254926890a477233910c8464142000f7c79e39b17a0b2c578285138898847422b10b08203f01d40da06943221700b00520274133092845c2080d104901bc0c005d02d81680b005702b015408c03e01e00dc050025011808804001f00f0074026010007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a86cfc666afd16cea7751da84d3b8934484a3e91828ac44d21910848304069fa4f8c7a53c99b00c66543283937c9504001ea8f1871a3781b30cc061c2fc16c8ad452427112f891446220f10307cc3ca1de0eb07403821bb0d986b434c1980c505e82d81650ac054829414409e84bc242119086035412407e03781800ba05b02d01600ae05602a811806e028012808c04402000f807803a01a00c004c022010007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00140
