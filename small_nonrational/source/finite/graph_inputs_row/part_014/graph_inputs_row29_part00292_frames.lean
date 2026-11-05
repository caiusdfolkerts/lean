module
prelude
public import GraphInputsRow29Part00292Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd63646b1ed8ceafe51428594049ae4b0a5652a494c4a2a4f926e930494a489236912485a3e11e28db3bc1a58d0466d2f19460a084f3270934497c4ac24d12208ee46722991048244021e80dd055229514209c84c424f11e88ac4322080fc07903a41a30c985842ac14f0a4050427413308f045c22010a06b823811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe2b69434499f4b4252fa9394729b6473a34d1808ad44d22210ec864429210906081d4059f64f9079430714aca345052410ecc73e38c1bc8d986a83421980c7861c2fc1748b5c54a29413008e43d81e40ee875c3a01c90e106ec3681ad0d3067432c1830be05982c01590a9052c28813d094048423411306d823811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x35d64ec858dad2538a59482714a093124a474889051f23b4708d51922d45488d102163bc6a0d119c2fa570ac1552a6540a694a28e510a093e2724d89792c244450798ef1d83a8738e41c23786d8d81aa340668c61862e45b8b616a2d0598b215e2b8568ac148208408650c81702d8560aa150298520a2140270330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3946aed45a52f7574ad156a8d4d89a132a634c09752d2574a89452724948c8fd1e2323e26d0d71a730e598b115f2ba568ab9542a2538a59482865009c9362584787e8f91ec3d0788ee1d63a0728e21be3686b8d019a30c608c017e2f85e8bc1722e05b8b615c228448690d01802f85a0b21602b8560aa150290330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x27897a5a95e3586e17851f8765d5749d0735ca721c5709bf6f1b76d1ad6a9a0635735bd6c541314b52a4a125489204751a45d1443d0c415023e0eb330c8314c3300bd2ecb82d4b22bcaa29ca0274932449023c8e2348c2248821c861f86c1ac5a164511404b12849120471184510c330c82a0a42408c220842007c1e070150500f0380d0300b0280901c060140400c0200400 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabda4ea3da309809038f38e68937f77df7ce7bf7a879b79078076f7607507397256ed6db6a161a59d58e58153e4bd4ab49d49048047546d4604524444364234133e63d83a73792e72d82cc2be2ac2a029628627526725a2472372091fa1cc1c21ba1ae1a019118315614613712b0c008808706906806005f05a05905805705605505405203303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5b1adf59aad50a9912fa5cc8e8ad13a23c428770d617c2884506e0a40b808fc1f3bd270cce197b245eeab55229d52ea35442814f29c9352624ae93d1ba2e4247f0d91a9344670c918d30e5fcbb9702ce574aa93c26645c8890d2104087e8f81ce3846e0d61561f43e0640c61702d8560aa150298520a2140270330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6cf66a65d6505d157656d55f52b4cb4be4b04aa49e49548f48347846c4654574484264193fa39833d3313292f229228427927126525c25324a23d23522c21c20f1ea1e11c11ac17116b16516115d15715414f14914313d13613012511f10f10c10a1051000fb0f60e50e00da0d40ac08007f06406305b05a05505405305205105004f04d03303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame008_links_0000 record000_frame008_links_0064)
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0657.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0657.count (({ width := 8, code := 0xd4cdcbc9c6bfbdbbb8b2b0aeadacabaaa9a8a7a6a4a2a09e9a98918f8d8a8482807f7e7d7c7b7a7978767472706c6a6462605f5e5d5c5b5a5958565452504c4a49484746454241403f3e3a39363534332f2e2d2c2b2a2927242322211d1c1b1a1918171514130f0e0d0c0b0a090706050403020100 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0657.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0657.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame009_links_0000 record000_frame009_links_0064)
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0657
    Papers.RationalityTen.SharedFrameCatalogue.group0657_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0656.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0656.count (({ width := 9, code := 0x11988c3615067f3e9eef475ba1cae371385c0df6f375b8d96b34da0c9632f974b75a2ad50a551a8942a04fa793a9c4ca59269044a1cfc7b3c1d8ea74399c8e270379b0d26631970b4592c15cac5529144a04f25110863e1e8ec74351a0cc6431180bc5a2813894481f0f074381b0d0642e150a03c1c0d0602c1409038180a04018080200 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0656.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0656.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame010_links_0000 record000_frame010_links_0064)
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0656
    Papers.RationalityTen.SharedFrameCatalogue.group0656_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
def record000_frame011_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc775f6af81792ae652fa9394709d549624612008ea46a230916089e446a1ed0e285d423a024fe87b037a1980ca86422f51594aae54429b14a0a3250827c93a89b64d226112bc90847122090046c435119e0ca462e30617a0b8c5a62c215c0a9852425b124883c3fa1ee0f007443861b90c305d82cc15106c023811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 11)
      (record000.inverseMaps 11) record000_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame011_links_0000 record000_frame011_links_0064)
theorem record000_frame011_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 11 :=
  of_group record000 11 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame011_indices record000_frame011_graph record000_frame011_links
def record000_frame012_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6d468067866d5fc5a85a059556051e51851150a5014fa4f34ec4e64df4da4d34cc4b74b049943f3dc3d33c938a32b32331930e3042f92f12e92e22da2d42ca2bd29f29327124c1ed1e51db1cf1c51bb1b21aa1a519d19618c17f16115513312912211b11510e1090f70f10eb0e50b508208106906806005f05a05905805705605505405203303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record000_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 12)
      (record000.inverseMaps 12) record000_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame012_links_0000 record000_frame012_links_0064)
theorem record000_frame012_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 12 :=
  of_group record000 12 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record000_frame012_indices record000_frame012_graph record000_frame012_links
def record000_frame013_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7176ce6c36b56285cd5c45b857d52551b50f5054f84ee4e84df4d94ce4c94be4b048f4854633ee39338a37e3432eb2e12d52c82bf2b42ad2a229d29428f28427625524b2292091b91b51ae1a81a019819018817f17717016a16414f14a13112d12812211c1161101010f90f30ee0ba08a08906906806005f05a05905805705605505405203303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record000_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 13)
      (record000.inverseMaps 13) record000_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame013_links_0000 record000_frame013_links_0064)
theorem record000_frame013_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 13 :=
  of_group record000 13 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record000_frame013_indices record000_frame013_graph record000_frame013_links
def record000_frame014_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1003.count (({ width := 9, code := 0x153a3512853a96cae53208a44a210f86c2e130782c0e02fe7e3dde8ed7436db2d76730980be5eaed72b75aacd62af562a94aa24da55128742a1104803f1f0f4783b1cce26c34988c05f2f174b85b2c15cac5528134984924104803b1d0e470371b0d46631180a4502311084401f0f07436150a03c1c0d0602c1409038180a04018080200 } : Fields).get c.val)
theorem record000_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record000) (record000.maps 14)
      (record000.inverseMaps 14) record000_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame014_links_0000 record000_frame014_links_0064)
theorem record000_frame014_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 14 :=
  of_group record000 14 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1003
    Papers.RationalityTen.SharedFrameCatalogue.group1003_facts record000_frame014_indices record000_frame014_graph record000_frame014_links
def record000_frame015_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1004.count (({ width := 9, code := 0x13b97cb657218ac4e230a7ebedf0f77a3c5deee76bb1d6e873385bcd869b1d8ac35e2bd5aaa54a9946a15027d3c9d4d261269045220f6793b1d4e46f369b0d66a34998c85f2e158a85329144a04f2612c944922104803d1e0e47033190c4602f170b4562914094481f0f074381b0d0642e150a03c1c0d0602c1409038180a04018080200 } : Fields).get c.val)
theorem record000_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record000) (record000.maps 15) (record000.inverseMaps 15) record000_frame015_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record000) (record000.maps 15) (record000.inverseMaps 15) record000_frame015_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record000) (record000.maps 15)
      (record000.inverseMaps 15) record000_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame015_links_0000 record000_frame015_links_0064)
theorem record000_frame015_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 15 :=
  of_group record000 15 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1004
    Papers.RationalityTen.SharedFrameCatalogue.group1004_facts record000_frame015_indices record000_frame015_graph record000_frame015_links
def record000_frame016_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1002.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1002.count (({ width := 8, code := 0xd5d0cfcdc8c3c2c0bbb5b3b1b0afaeacabaaa9a8a7a5a2a09c9a9594928d8785838281807e7d7c7b7a797774726e6c66646261605f5d5c5b5a59585653514d4b4a49484746434241403e3b3a373633322f2e2d2c2b2a2927252421201d1c1b1a1918171513120f0e0d0c0b0a090706050403020100 } : Fields).get c.val)
theorem record000_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record000) (record000.maps 16) (record000.inverseMaps 16) record000_frame016_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record000) (record000.maps 16) (record000.inverseMaps 16) record000_frame016_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record000) (record000.maps 16)
      (record000.inverseMaps 16) record000_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame016_links_0000 record000_frame016_links_0064)
theorem record000_frame016_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 16 :=
  of_group record000 16 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1002
    Papers.RationalityTen.SharedFrameCatalogue.group1002_facts record000_frame016_indices record000_frame016_graph record000_frame016_links
def record000_frame017_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x3866c4d71aab34620c29832ee590b1560abd56eac556aa5542a754ba925189f13b26446881d019fd3c26d0d79aa34c67ccd99932863cc49842fc5e4b61682b65389091d22e444861082083f47c0f51e23ac728d91a8320618c21782dc5a0ae14e2904f89b1041ac3505d0b81582a85009e1382684c096128240330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record000_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 17) (record000.inverseMaps 17) record000_frame017_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 17) (record000.inverseMaps 17) record000_frame017_indices (Fin.ofNat record000.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record000_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 17)
      (record000.inverseMaps 17) record000_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record000_frame017_links_0000 record000_frame017_links_0064)
theorem record000_frame017_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 17 :=
  of_group record000 17 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record000_frame017_indices record000_frame017_graph record000_frame017_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (Fin.cases (record000_frame011_supported hcells) (Fin.cases (record000_frame012_supported hcells) (Fin.cases (record000_frame013_supported hcells) (Fin.cases (record000_frame014_supported hcells) (Fin.cases (record000_frame015_supported hcells) (Fin.cases (record000_frame016_supported hcells) (Fin.cases (record000_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c72d796a83509a68d1f688b429a08cfc678b3a97aeb695a32c895e2aca55b2a3d4e2a5e4fea76936c9854af252924690547923bd1d08e146d234d1988c345f22d515c8a444ea25911e78038e1bf4dba6a334099c8cc6632310971cb505882a714b0a3a50e26e93309904c125d12cc95a4a6250924c91848323d91d48de46c1f80f0873035a1978c705ca2d115c8aa453228a13d09ac4aa23611388283f81ee0f4075838c1b60d3865c3101720a9851024e11908584141ee0f007483881ba0d505802bc13809b03881bc0dc062030017c0680330190094048023006002c0140090030014008003 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame001_links_0000 (interval_append _ 64 128 142 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x19fcc9f6363149874c145fd2fc17d2bd05d5ae5562cad255caa99504a6b530a8f5436a084e1a69931c95e49da4b920e8e446723151668a144821f90e485a42620bd0347ff3f51f50f7c7273729b2cd686853341980cae62930c1780b925b32c515b8aca55c2981488a3850b27e13b49bc4d326792a0934487236117089a4491fa0f6077e38e1b70d8c6643201830bd05c62d31610ae054427b134891446422010b87f43dc1e00e8870c3721a40c085c429a13e097049821e0ff07903941b60ca05502a413809b03881bc0dc062030017c0680330190094048023006002c0140090030014008003 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame002_links_0000 (interval_append _ 64 128 142 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8037be7a779c79278177677276e76675b7546fb6ca6b76a968d67a67365a64563a60f5ff5ee5d65c25b859f58b57f57c57556e56756055b55354e54453d53452d52651f4a747345f45042e41640f4073e13d63a739738336134d34233a3143093073002f92f22eb2e62e22d42cd2c52bc2b52af2ad27625f24922620e2051e31d91cb1c31bc1b51ae1a819b18b18216c16615d15b14b14313c13512e12811b1091030ec0e40df0db0ce0c90c30c00bf0b80a40a309a09907106f06e06206005f03403303202502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame003_links_0000 (interval_append _ 64 128 142 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x297d109f93d676cde9ad346654c697d2de424698c1156224378630960ec187f4fc9f4bdb79af19dbbad752e9dd1b9a72ee35c4b7d6f4dc5b4b626b0d41a43125f2bad702cb586aed5b2ab54ca293f2704ba95927a494768dd1aa2f4588890f217422804fc9ef3ca77ceb9d636c6a8cf18d3005e8b39642c0574ab95129851c9f1312544708b10f21c428841031fa3dc788e71b234c628be1702dc588ac14e2885009c124244440870ce198328590b015c198320620941202301802c0500900c01402003 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame004_links_0000 (interval_append _ 64 128 142 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x298d109ff3de78ce59bb36669cce9913124ac848fb1da354618b9146244438570860ac047eefbdf0bd479af29e1bbb76eec1d6ba7744e6dca38b704de9b933c642c4983af35d6b896eacb588ad1552a1528a3d442854f29d138a684c69712ca544a09011c22d4508890da193f47a4ef1ca3786d4d119e332648c51842f65d4b795f2b051c9e9352624a09111b226434820fb1d03806a0cb1883005b0b01582a05189b11c234440870ce198328590ae1581802f05c0901182201802c0500900c01402003 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame005_links_0000 (interval_append _ 64 128 142 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x2df5a7b2362ac2577ae15aab255faa95328a4f99db38e6a4c49712b65149b9091e6384618a71261ec3185309e11c1982d03202bfb7f2fc1f4be17acf39e13866ced5da5339660ca191b1361abd572ad958eaf95c2b3542a6d4ca91516a0d402774e69892b24d4868f11aa344007b4ee9c93766b8ce194316614be1742d8594ae94c2824c89411e23645c8990b20a3fc7c0f11ce3806a0cf1903145f0b81642ac540a312824c450890d41a43405c0b41641a0330640941202301802c0500900c01402003 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame006_links_0000 (interval_append _ 64 128 142 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x83d8027e27d17c57b07a379778f78777876e7176f36e96dd6c96b56aa69868a68065864663361d6065f75e25ce5c05bd5b65a75a159258857b57656a55f55454653b52b4cd49c4864714544444384304114063e43d13bf3ac3a539d39637e37637336535b34f34a33e3373213113032f82ed2e32e12aa29327c25e24a23d22421b20f2071fb1f11e71dd1d11c11b719f19518818317917116415a1521471391211151040fb0f20ed0e20da0d10c80c20ba0a20a109409306e06c06b05f05d05c03303203102502402300c00b00a009006005004003 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record001_frame007_links_0000 (interval_append _ 64 128 142 record001_frame007_links_0064 record001_frame007_links_0128))
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1d3edb06a734999fecc9651b23589cc3a5a5aba5582a9a53228f94509e94eaa6a133498c4bba5a52c494f4a424fd270931495248d238911487240d1f88f9477239d1c08dd3e91da4e8271636d1ad4d3e6653271748b585862a794aca304df26793109644a024711f48da44d22490a88364181fd8fa47b23d71b18cf462e2e015e0aa44e026012a890c46221f10707f83bc1da0dd86b035218c0bd05a82d01570a8052428413b09a04ac24c11d08b044421210307e03dc1e40ec07303801b40d404a024812208f04702340e206f03701b00d606a01500a004e025012008c02a013009004001e00e } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame001_links_0000 (interval_append _ 64 128 142 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8bb88085e85284583382982280d80679574e7387227046ed6e46ba6ad66664e6346145f85ec5c05ae59959058858057857056256055154954653953152a5274b246c45443a41a3fe3f23c63b436034a3343162ff2f62cc2bf2b62ad2a529d29528d27f27d26e26626325624e24724421a20d2001ec1df1d81c11bb1b81b11a91a219a19118518217616e16a15f15815014d14613f13713012811f1131101040fc0f80ed0e60de0db0d50d10cd0c90c50c109409209108f08e08d07106f06e06c06b06a02a02802702502402301501301201000f00e } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame002_links_0000 (interval_append _ 64 128 142 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x7e1f1791de765d5745cf71dc46fdb26b1a768d9f67595649835f9795d1705b968591605795c56958559535494f5354c52547515444f92d4a1234791a46112439003e8f53c4ed3ace3380df374db364d7354d2344ce330cb320c6310c32dcb12b0a8290a22689725894248902388c22488214832087f1f47b1e8781d8741c8701b86b1a867194641845f1745c1685916057158551043f0f83c0ec3a0b02a0a4270982505c150501204410020060140300801 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame003_links_0000 (interval_append _ 64 128 142 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x8861d84e1083208812027e9f77d5eb7a1e4781dc769d273dc4705bd6e5b56cdac699a16799b661956498d63187611835f97b5e5785d16759160571585594f5253d4e9364c92e4b124485204751a45d144450c42d0640d023f4fa3e0f73b4ea398e2378dc350d1340cd328c7310c12f0bb2d8b32c8ad2a8a829ca42849e26c982549023c8a21c862047e1f07b1e0771d8751d073190621845f1785d1444f1384c12c4a0a82809c2509023054130481003c0e } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame004_links_0000 (interval_append _ 64 128 142 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x8861d84e1083208812027e9f77d5eb7a1e4781dc769d273dc4705bd6e5b56cdac699a16799b661956498d63187611835f97b5e5785d16759160571585594f5253d4e9364c92e4b124485204751a45d144450c42d0640d023f4fa3e0f73b4ea398e2378dc350d1340cd328c7310c12f0bb2d8b32c8ad2a8a829ca42849e26c982549023c8a21c862047e1f07b1e0771d8751d073190621845f1785d1444f1384c12c4a0a82809c2509023054130481003c0e } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame005_links_0000 (interval_append _ 64 128 142 record002_frame005_links_0064 record002_frame005_links_0128))
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x92e448de318b2288922286a1784a057fdfa7d9f27c1e8795d6745cc71dc3705ba6d5b06b9ab6a1a56899d67197651936398c6298960d725b56858d5f57556545424f1374cd2f4b5254892147d1c4651644d0e43508415043fcfd3ecfa3b8e838cdf36cd9344ce334cb320c5308bf2e8b92d0b12c0ab2a4a7298a42889f27099258912408b22087208801f87d1ec7a1e4781dc761886017c5d1705b1344b1284811c460a82809c2509023054130481003c0e } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame006_links_0000 (interval_append _ 64 128 142 record002_frame006_links_0064 record002_frame006_links_0128))
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x19feca0632b12d86ec0c5f92fb575eb9958a2b49572aa653e29954bea1f50627253589914b024f525e8f8471232516e8a544a22090e8857428a0b102e8113f61f58f807ba3931b9cd9a6b534619bccc6638313976cb885b12c515b8aca534293147ca1a4fe27793809a84bc25b926c91a48a23491688964481f80f5077a38c1b60d8864e3151850be45d02d81638ae854229a13d09a04c2241117887442c2000f8878c3a81c60dd06983361820b905a429813d096849023210907c83b01be0cf04a024812208f04702340e206f03701b00d606a01500a004e025012008c02a013009004001e00e } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame007_links_0000 (interval_append _ 64 128 142 record002_frame007_links_0064 record002_frame007_links_0128))
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x72a6ed6ca6ba6ae69868568065f6506155f55e65d65bf5b15a858457855b54f54453252552050e5054fb4f54ee4e84e14dc4d24cf4c34bb4b84ad4a549d49b4574394254113f93e63df3c23b537e36935d34332f32b30c3022fe2f32ec2e42de2d62c72c42af2a42a228d28427827623f23121f2021f41ed1cd1c31c01b41ae1a71a019818918616e16616414f14313a13812a12311c11610f10b1030fe0f50ef0ec0e40dd0d60d20ce0c80c20bd0b80b108808608508308208106f06d06c06a06906802a02802702502402301501301201000f00e } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame008_links_0000 (interval_append _ 64 128 142 record002_frame008_links_0064 record002_frame008_links_0128))
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x2734d398d2fa5acab94928248c8b8bb1121b42d83f04e08bfd7eaf7de8bc376cea9d138b704de1b936c6ced85ae35069ad059cb3865cca5913205deb6165abc55ca8d4da844f496d28a4546c8b914a1241a829019fd3f47d0f71e23be748e59ca3806e4da1b2330640c31782d8598ae1572a853ca51452824ec9993124e4788e915220424839011f83e07a0ef1d03806f0d3198328610bc16e2d0578ad1542904f09b0fc1f03d8790f01dc310600be1742e05b0540a01382504808c0a8130240400780e } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame009_links_0000 (interval_append _ 64 128 142 record002_frame009_links_0064 record002_frame009_links_0128))
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
def record002_frame010_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0998.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0998.count (({ width := 9, code := 0x21d0d85c2a13078341602ff7f3f1f6fa7c3ddecf2783b9daec753a1cce270379b6d96bb55a6d16833596ca6431d8cc56230982c05f2f174b65a2c560af56ab156a752a91429f4ea6d32974b24d229047235188b44a210e854220cfe7d3e1e4ee75399c4de6e359a4d06632990c6622f974b6592b954a85127938984b251249047231148843209007e3e1e8f072381b8d86a34108803e1e0e8702612088401e0e } : Fields).get c.val)
theorem record002_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0998.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record002) (record002.maps 10)
      (record002.inverseMaps 10) record002_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame010_links_0000 (interval_append _ 64 128 142 record002_frame010_links_0064 record002_frame010_links_0128))
theorem record002_frame010_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 10 :=
  of_group record002 10 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0998
    Papers.RationalityTen.SharedFrameCatalogue.group0998_facts record002_frame010_indices record002_frame010_graph record002_frame010_links
def record002_frame011_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0997.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0997.count (({ width := 8, code := 0xdbdad7d6d5d3d2d1cdcbcac7c6c5c3c2c1bdbbb8b7b6b4b3b2afadaba9a8a7a6a5a4a3a09e9d9b9a9998969392918f8e8d8a88848382807f7e7a78777574737271706f6c6a6967666564605f5e5c5b5a56545351504f4e4d4c4b484645434241403e3c3b3a393837363331302e2d2c2b29282726252422201f1e1d1c191716151413100e0d0c0b0a070504030201 } : Fields).get c.val)
theorem record002_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0997.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record002_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 11)
      (record002.inverseMaps 11) record002_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record002_frame011_links_0000 (interval_append _ 64 128 142 record002_frame011_links_0064 record002_frame011_links_0128))
theorem record002_frame011_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 11 :=
  of_group record002 11 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0997
    Papers.RationalityTen.SharedFrameCatalogue.group0997_facts record002_frame011_indices record002_frame011_graph record002_frame011_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (Fin.cases (record002_frame010_supported hcells) (Fin.cases (record002_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1cb6d9b6a134b5a4cd1f68c3445a14cff67e33d59d4bff5a32c55606af156f2b2956ca96547a9f94bc9da4d4a65d30a9724af252925492348923c91de8e8470a3691a68cc461a2f916e8ae455a29113a8964479a8cd0267232c9930c7254e2961474a084f727212e895a4a6250126092248824211ec8ea46f2348d6865e31c1870bcc5ba2c214c89e84d625612608f044420a0fe07b83c01b60cb86202e61690ac84fc24e11908583f41f20f007483881b60d505902bc13c09b03881b80c405f02000d806803301900c404e025012008c04401200580280120080028010006002 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame001_links_0000 (interval_append _ 64 128 138 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2fadb6b195e2ba56ead3596b0d56aa753aa251b9c134666cc79852fa5d4af95929e4ec738c91762ac4f89310e1cc3585b0920fc1882102a023fe7e8fc1f43df7b8f61ea3d0798d4da4b44678ce198ac957caed572a9544a0d3b2714d89792a2464868e119a2e450724de1b7364690cd18c2ec5acb415b2ac53ca19382664b8941152124087d0f51dc38c6c8d219c320628bb1682c0550a7132258448860d01942c85607e0d81a0330640c41382504808c110120160280480800a01001802 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame002_links_0000 (interval_append _ 64 128 138 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0x32188bfdeaf176ba5cae36eb6daed163add5aa952a853a9b4aa4d1e89409dce66f3599cca5f2e964a651269248a411f8e46e33168ac52271288bf1f0f77a3cde0df6db69aed669b258ac3612f976b75b2cd62b057281389a4ca55248e44a150881401f4f075399c8e06b33998c6622f968ae552a148a24e2612c9248200f46c33160a446200e86830170b0542410078381a0a0401c0c05018080200 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame003_links_0000 (interval_append _ 64 128 138 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0x2d969b358ec35eadd66af52a8d3e9549a350e833e9dce66f3298cbe552993492431e8e46a2b1489436190a83c1205007dbe9f0f3793c5e0ef77399c8e37037dbcd66a34da0cf6731982be5e2e56cb1582b958ab552893a9a4c255248d44a1d0c8341204fc7c3d1e4f074391c4dc6d361a4ce653218cc4602f174b85b2b954a24f231107639158a04c251208c401e0e8703612058281208028100602 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame004_links_0000 (interval_append _ 64 128 138 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0x37db8d8eb757a8d2e8f439ccde672991c5e1b0981bf5f2f575ba5cadb6ab3592c35eae56aab54a9536994aa3d1285409dcea7133994c6612f97476371a8bc5a29017ebedf0f57939dc4df6eb65aacf6733194c9642ed6cb358ab552a34d25928914722d0c8441205007b3c9e0ea74391b4d6693419ccc6431184c05f2d15ca651241187839158a04c251208c401e0e8703612058281208028100602 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame005_links_0000 (interval_append _ 64 128 138 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0x32188bfdeaf176ba5cae36eb6daed163add5aa952a853a9b4aa4d1e89409dce66f3599cca5f2e964a651269248a411f8e46e33168ac52271288bf1f0f77a3cde0df6db69aed669b258ac3612f976b75b2cd62b057281389a4ca55248e44a150881401f4f075399c8e06b33998c6622f968ae552a148a24e2612c9248200f46c33160a446200e86830170b0542410078381a0a0401c0c05018080200 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame006_links_0000 (interval_append _ 64 128 138 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1082.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1082.count (({ width := 9, code := 0x297459fcee75389b4d66931984ba57289147a3b1b8cc622f1489c461d0b83c1a090280c01fafc7d3ddecf579bc5e0ef763add2e672b91c6e270b4da0cf6632d90bb5c2dd68b35829d4aa35127936984ba51249147a150681401f0f276391bcdc6b3519cc45f2e970b456299489e4e259188641200f87a3a1c0dc6a34180b452261107c36180b858281309044200e06830160a0401c0c05018080200 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame007_links_0000 (interval_append _ 64 128 138 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1082
    Papers.RationalityTen.SharedFrameCatalogue.group1082_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbf4ba0b5eb33b29b22b19b0baffae1adbaccaaba60a019da9cb9c29b89a599697a9729639468f88c88b68aa89e88c87c85c85183d81c8138037f87ed7d77c37a879978476976374f7387217096125fb5f05dc5d45c852750e5014eb4e14d349c48547a47045c44d43843341840a3f93eb34e3343223142fd2ed2d32ad29328626f26525523b2212111ff1ee1cd1b51a819218717815e1411311211111080f50e80da0cb0c00a90a809c09907106e06205f04003603403303203102702502402302201200b00a009008005004003002 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame008_links_0000 (interval_append _ 64 128 138 record003_frame008_links_0064 record003_frame008_links_0128))
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7a176c74773973473072a72472071771470e7046c267f66a65d65664d6416386256236156015d45bf5b75ab5a259759057a57757055655354c54754153c53752f52a52451c51951350c5054fe4394224194084013f738036a36334f34934031e31230d3093012fb2f32ef2e52df2da2d425223f23422b21c20f1f81e21d01c71b91b41a919518417b17116514e13b13512511f1171010f00e80dd0d10ce0c50c00bc0b60b109e09c09309106f06c06005d03e03503303203103002702502402302201200b00a009008005004003002 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame009_links_0000 (interval_append _ 64 128 138 record003_frame009_links_0064 record003_frame009_links_0128))
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
def record003_frame010_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2fb5bfb255eeb9d6fad158aaed53aa352ea05109ad31a61cbc96b2be55ca093b26646c6c8b313e244428790da1642883d052074087fcfe1f8bed7c4f75ebbca78ef0dde3b5762cc594323638c61892b4554a894ba9651a9bd3025a4a891d1fa2d4548850da174206d0d319f332630c11722c6558aa1462824f8979232404708a9031f23d0760e81c2358670c81882f45c8b015629c5009c11c234420820d61a43005d0800d81a0330640c41382504808c110120160280480800a01001802 } : Fields).get c.val)
theorem record003_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record003) (record003.maps 10)
      (record003.inverseMaps 10) record003_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame010_links_0000 (interval_append _ 64 128 138 record003_frame010_links_0064 record003_frame010_links_0128))
theorem record003_frame010_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 10 :=
  of_group record003 10 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record003_frame010_indices record003_frame010_graph record003_frame010_links
def record003_frame011_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0851.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0851.count (({ width := 8, code := 0xbbbab9b8b7b6b4b3b2b0afaeadacabaaa9a8a6a5a4a2a1a09f9e9d9c9b9998979594939291908f8d8c8b8988878685848382817e7c7b7978777472716f6e6d6a676665636261605e5d5c5b5855545351504f4c4a49474645444241403f3c3a39373635343231302f2e2c2b2a292826252322201f1d1c1a1816151413110f0e0d0c0a0807060503020100 } : Fields).get c.val)
theorem record003_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0851.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record003) (record003.maps 11)
      (record003.inverseMaps 11) record003_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame011_links_0000 (interval_append _ 64 128 138 record003_frame011_links_0064 record003_frame011_links_0128))
theorem record003_frame011_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 11 :=
  of_group record003 11 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0851
    Papers.RationalityTen.SharedFrameCatalogue.group0851_facts record003_frame011_indices record003_frame011_graph record003_frame011_links
def record003_frame012_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0849.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0849.count (({ width := 8, code := 0xbbbab9b8b7b6b4b3b2b0afaeadacabaaa9a8a6a5a4a2a1a09f9e9d9c9b9998979594939291908f8d8c8b8988878685848382817e7c7b7978777472716f6e6d6a676665636261605e5d5c5b5855545351504f4c4a49474645444241403f3c3a39373635343231302f2e2c2b2a292826252322201f1d1c1a1816151413110f0e0d0c0a0807060503020100 } : Fields).get c.val)
theorem record003_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0849.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0849.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0849.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0849.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0849.localPairCheck (smallEmbedding record003) (record003.maps 12)
      (record003.inverseMaps 12) record003_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame012_links_0000 (interval_append _ 64 128 138 record003_frame012_links_0064 record003_frame012_links_0128))
theorem record003_frame012_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 12 :=
  of_group record003 12 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0849
    Papers.RationalityTen.SharedFrameCatalogue.group0849_facts record003_frame012_indices record003_frame012_graph record003_frame012_links
def record003_frame013_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0848.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0848.count (({ width := 9, code := 0x23d1d8e46e33178a44a210c85c260d058240e02ff7e3e9f0f479bc5dced763a9d0e571b85badc6d35dacd46933d9acb63b1988c1602fd7cbd5e2e56eb65a2cd64ae562ad52a853a85389a4c255269047a35188b45215007e3e1e4ee74389bcdc6c359a8d06632990c6602f174b65a2c95caa5429948a24f27134984b249208c451f0f46c35140984823110843e1d0e06c3412058281208028100602 } : Fields).get c.val)
theorem record003_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record003_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record003) (record003.maps 13)
      (record003.inverseMaps 13) record003_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record003_frame013_links_0000 (interval_append _ 64 128 138 record003_frame013_links_0064 record003_frame013_links_0128))
theorem record003_frame013_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 13 :=
  of_group record003 13 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0848
    Papers.RationalityTen.SharedFrameCatalogue.group0848_facts record003_frame013_indices record003_frame013_graph record003_frame013_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (Fin.cases (record003_frame010_supported hcells) (Fin.cases (record003_frame011_supported hcells) (Fin.cases (record003_frame012_supported hcells) (Fin.cases (record003_frame013_supported hcells) (fun j => Fin.elim0 j)))))))))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb20b06afaaf3ad6ac7ab79d79c89c19b59a399497d96f9609518a888687686184b8378247f77d47c07aa79678176e75a7407297126fc62b61d61360b5fe5f35dd5d75cb5bc52750e5014ee4e14d34c449b48247746645944a43d42d41b40d3fc3ee36b35834d34133131f2fa2ea2d82c72b72ad2a12932862652552462322232132011f01cd1b51a819718717816b1561030bf07b07105d05c05b05a05805705605504303902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame001_links_0000 (interval_append _ 64 128 135 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x303d7eabee5f42f2d768b9e54daa2d4fea745342981490a3a51228452b293649624592028ea46a22790f687142e212506881f4059fc8fb87c63d79a9cd3268833e19accc264e32218c8c4258a2b71594aaa54529b14a09f24db26913049624a224a12188de45f228110075a39b1c60dec6d836219e8ca462e30617a0b8c5a62c215c0a5050226f12c891c46822210707803861b90d5066030c1760b2844019207b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame002_links_0000 (interval_append _ 64 128 135 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x34dd1f44cff36cc72cbcef0bb6eab9ee4b76d9b56d1a9a9ea6a91a26829ee739ba6b9865c9524c90e3d8e2338c1ff7f5fb7e5f77d5ee7ade6785c06f1ba6c5ac699a065d93645855fd785c569591615795a4e1344c12d4a52645d1142d0640d003f8fb3e4eb398e1360d4340cc324bd2d8b32b0a527c9924073174501303e0f43c0ec390e0370d8340c0220842007c1d0701b068150441003c0e0340c02c0a024080140400c0200400 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame003_links_0000 (interval_append _ 64 128 135 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x25393e4d92a4690e40852128420d82e0881603805ff791de76dd6749ce729c4701be6e9b66c5ac69da46859e66d765d1725c16e5b16759561575434fd3d4e9384d5324a9264911f46d1543d0a41d0540d00390e1378db360d5330c6300bb2e4b72d4b32c4a92909f2649624c902388720c811f8791d06f1a45a13049114390e0370d8340cc320c4300b01e0741c06c1906017058150441003c0e0340c02c0a024080140400c0200400 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame004_links_0000 (interval_append _ 64 128 135 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0725.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0725.count (({ width := 9, code := 0x5a2cd64b157eb959a652e9347a2d0a813e9e4ea5f2b9449a47208ec5e271187c2e110581c05fcfb7c389c2e06f375b6d86bb51a2c5613017cbc5cad95caa54299469f4da5d2c944923d0e864220d027f3e1e4ec74399c8e270379b4d66933194c6612f96cb2582b954a65127110783a1c8d06632188bc5c2d160ac4e1b0d06430160a8502612088401e0e06830160a048200a04018080200 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0725.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame005_links_0000 (interval_append _ 64 128 135 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0725
    Papers.RationalityTen.SharedFrameCatalogue.group0725_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x32a993ac966483221902c7a56dab5559cac75602ae5560aab5522a7530c9644a9a4f525a91b485234d1628a044521e90d0857426211107a83641799f0cea66f3341984cb46513261914c7e55f2a194d4a4651828513f09a44b6254125891647d23791988c045b22b11446da35f1a78cfc66031f17f0bb85ba2cc15f0ab853c28f13f097449a23c11888a844621c10a878036e1a20c685f02d41570a384281a407b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame006_links_0000 (interval_append _ 64 128 135 record004_frame006_links_0064 record004_frame006_links_0128))
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6d96ce6ca6c66be6b96b461260e60b6055ff5fb5f45f05eb5e656d55554a53d5305235194f94e34da4c94bd4b24a549b49248c4874803ee3ea3e73e13dc3d83d23cf3ca3c435834833e33332d32231b3032f22ed2de2d72cf2c62bd2b72b32af2aa24523e23923022621b2091fd1f41ea1e41de1d51c91c41ab1a519918f18a18618117a15f14613a12d11f1131070fb0cd0a207106a05905805705605405305205104103902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame007_links_0000 (interval_append _ 64 128 135 record004_frame007_links_0064 record004_frame007_links_0128))
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x67a67367266d66565f65b5d55ce5cb5c65c35c05b85b45ad5a853b52c52951c5115095004e84d84d14c44b94b24a94a249a49348f48b3c53c03bb3b73b23af3a73a339d39932831b31830c3022fd2f62dc2cf2c92bd2b32ad2a72a129b29629329022c22521e21520d2091ef1e81e01d51cc1c41c01b91b219819018a18217b17417016c14f13d13712a12011610b0ff0d50ae07706f05b05a05905805605505405304203902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame008_links_0000 (interval_append _ 64 128 135 record004_frame008_links_0064 record004_frame008_links_0128))
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0751.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0751.count (({ width := 8, code := 0x868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0751.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0751.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame009_links_0000 (interval_append _ 64 128 135 record004_frame009_links_0064 record004_frame009_links_0128))
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0751
    Papers.RationalityTen.SharedFrameCatalogue.group0751_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x35cda86d2b68db3f19c8ccd5642ad1540a8c53ba989490a3b513a84d23c8fa473a3451828ad44d219108483040e2034ff67e93ed9f18f6a7a53c99650b0056c2ac150ca5c51428393cc9be3ea1e30ecc73a38d1bc8d9866030e17e0ba05b22c715a8a9c524281138897c41e20810087e83e61ec0ef075c3a01c90e106ec3681ad0d3066032218a0c085e82e616c0b2854828813d09a84bc25012108c83d81aa07b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame010_links_0000 (interval_append _ 64 128 135 record004_frame010_links_0064 record004_frame010_links_0128))
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x65f64f64564063462761959058858257b5735665595555485404df4cd4c24b44ab4a049748047046645a45544843e43442841e41540d38938137a37336836235134a3413382d72c32bb2ac2a129728f27826625f25224a24023622c21e21520d2051cb1c51bf1bc1b71b01a419d19618f18918418017a17316615e15715114b14313d13912711d11610e1070ff0f90f20d30b207206b05705605505405205105004f04003902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame011_links_0000 (interval_append _ 64 128 135 record004_frame011_links_0064 record004_frame011_links_0128))
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6e06d56cf6c96b76aa69e5f45eb5e45db5d35ce5be5ba5af5a253d52a5255195105054f84df4ce4c94bd4b24a749a49148347946d4623ba3b03a83a239b3943843803723683012f22eb2df2d62c82bf2a229428f28327826a25f25724923c2322281e11d91d01c81bf1b91af1a81a019819018817f17717016615f15714d14814013713012211611010c1081010f90f20d40b407906f05b05a05905805605505405304303902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame012_links_0000 (interval_append _ 64 128 135 record004_frame012_links_0064 record004_frame012_links_0128))
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
def record004_frame013_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0758.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0758.count (({ width := 9, code := 0x4da6933994c25f2e8c45e2d158a44e230f86c2df2f579bbdd6e872b89c0df6db69b0d66a349a2d067ae570b75b2d568b2582b9589a4b251208c44a190681401f0f6793b9d4e672389c0d26732990c4612f174b85b2c95cac54299409e4e26930964a2491082401f0f4783b1d0cc642e168a8522813894482311084401d0e06c34180b8582a110803c1c0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record004_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record004) (record004.maps 13)
      (record004.inverseMaps 13) record004_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame013_links_0000 (interval_append _ 64 128 135 record004_frame013_links_0064 record004_frame013_links_0128))
theorem record004_frame013_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 13 :=
  of_group record004 13 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0758
    Papers.RationalityTen.SharedFrameCatalogue.group0758_facts record004_frame013_indices record004_frame013_graph record004_frame013_links
def record004_frame014_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0x4da6933994c25f2e90c823f1e8ec7235198c45e170782c09fefd7dbe1ecf5793c5e0ef773b1d6ea74b71b6da6cb61aed56a34da4c6613017aba5c2d966b1582b558ab552a54ea652a912c94492411c8c4421908813f9f4f6793b9c4dc6b34198c8623096cae552913c9849228ec6c34180b4582b150a04e2612890401d0e06c34180b8582a140803c1c0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record004_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record004) (record004.maps 14)
      (record004.inverseMaps 14) record004_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame014_links_0000 (interval_append _ 64 128 135 record004_frame014_links_0064 record004_frame014_links_0128))
theorem record004_frame014_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 14 :=
  of_group record004 14 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record004_frame014_indices record004_frame014_graph record004_frame014_links
def record004_frame015_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1a8b4c693d1fa2340e7bb8b702dd5b4b5f6aad0d9cb2b63e89cff9f13aa71cda9a32ce4ec9690f2023b46c8c516a2a450894e59c8b8b70ae01bdb726dad99b02e459cb1d5c2b154ea753f26a4c6955272454788cd15a2544286cee1d539c718e01b8352688cd992316610be1762dc57cac151294518a113e2744ac8f118222430839021f2348570780de16c2d0590b01582a8540a61081c82504808c1102003e0780e8150220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record004_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record004) (record004.maps 15)
      (record004.inverseMaps 15) record004_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame015_links_0000 (interval_append _ 64 128 135 record004_frame015_links_0064 record004_frame015_links_0128))
theorem record004_frame015_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 15 :=
  of_group record004 15 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record004_frame015_indices record004_frame015_graph record004_frame015_links
def record004_frame016_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x10a61041e83b05e0940f772edddabae752e95d039c72ae41b03576a2d29a3b40678cb99231e62ac4584b035fcbdd782ec5cea494828e50ea053f2794e89bd34a3745689d0f218424831001f53e67a8f29e13b875ce71c938a700c818d30e608bd9722cc57cac15429a520a193b26a4a090119228440859072063d8768e61c0364688cd18a2a04686c0ca1482885009e1342604b0940fc1b82504808c1102003e0780e8150220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record004_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 16)
      (record004.inverseMaps 16) record004_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame016_links_0000 (interval_append _ 64 128 135 record004_frame016_links_0064 record004_frame016_links_0128))
theorem record004_frame016_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 16 :=
  of_group record004 16 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record004_frame016_indices record004_frame016_graph record004_frame016_links
def record004_frame017_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x12b6544a79492724bc9282f04606c09809009fcbf37daf99d4b9d738e51c6b88700dc5b4b646b6d51a7347682ce599b2d652ab553aa253ea6d4c28f512a093f23f4668c51422143284d019fb3ee7bcf41e03ba75ce79c73846fcc61853005e8ba9712c456cab14f2925109f93a2684949011822643c849031fe3d0750e61c437c6d0d31962cc4e06b0ca150298520a213c2704d0980f41a82504808c1102003e0780e8150220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record004_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record004) (record004.maps 17)
      (record004.inverseMaps 17) record004_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame017_links_0000 (interval_append _ 64 128 135 record004_frame017_links_0064 record004_frame017_links_0128))
theorem record004_frame017_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 17 :=
  of_group record004 17 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record004_frame017_indices record004_frame017_graph record004_frame017_links
def record004_frame018_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0750.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0750.count (({ width := 8, code := 0x868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0750.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0750.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0750.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0750.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0750.localPairCheck (smallEmbedding record004) (record004.maps 18)
      (record004.inverseMaps 18) record004_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame018_links_0000 (interval_append _ 64 128 135 record004_frame018_links_0064 record004_frame018_links_0128))
theorem record004_frame018_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 18 :=
  of_group record004 18 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0750
    Papers.RationalityTen.SharedFrameCatalogue.group0750_facts record004_frame018_indices record004_frame018_graph record004_frame018_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (Fin.cases (record004_frame013_supported hcells) (Fin.cases (record004_frame014_supported hcells) (Fin.cases (record004_frame015_supported hcells) (Fin.cases (record004_frame016_supported hcells) (Fin.cases (record004_frame017_supported hcells) (Fin.cases (record004_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xccc65332418d2c5361fa99d482a2b50227b93b49764b425852b29534a6251527c93749824a524491b486a4191fe8ef47423851b46d63579a64cde659322153ca5651828213d09c24d125f12b093448823b919c88643221190007de3df1e78b805782a914a8a144e426212788f445621910407e03a81c30da06443001700b0055829e1480a084e826612508f045c2200d104a01c40c405d02e016c0b405902c015c0ac05501c80a804a024011808804202000f807803a015008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame001_links_0000 (interval_append _ 64 128 129 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd736a1b4ad9f8ce4666aa814eea6251da89d42691e47d239d1a68c1456a26911087643221490848304069fecfd27c63da9e94f2656c2a194b8a0e4f326f8fa878c3b31cf8e346f23661aa0d0866031e1870bf05b22c715a8a4850227112f88043e61ec0f207783ae1d00e487083761b40d686983301910c505e82e616c0b285802b21520a5851027a12f09404842340d504a01c40c405d02e016c0b405902c015c0ac05501c80a804a024011808804202000f807803a015008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame002_links_0000 (interval_append _ 64 128 129 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x33a660ca98eb17622abd52a9f524a31432594a69412624a48e91120a3e4768e11aa324588a51321e4368610a9bb3626accf198324594af95c2b0558a995029a528a39442824f89c1352644a8939242423f07b0f31de3b4750e71c83846f0db1b0354678cc1923045f0bb1702dc5b0b51682cc590b015e2b8568a31101ac2e0570ac1542a0530a41442804f0720a8128240460881082003e0780e81502003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame003_links_0000 (interval_append _ 64 128 129 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x36d6c0d69a634667eb4161abd55eaa5512754de9b1342664c69812ea5a4ae95128a4e4909152123a46e8d1189ca37a6dcd49a33385bcb49662c4580ae95a2ae550a894e296520a113f2784d09892e256418800fd1f23dc7a0f11dc3ac740e51c437c6c8d61a632c640c5184304600bf17c2f45e0ba1722e05b8ad1201bc3005b0b41642c0570ac1542a0530720a8128240460881082003e0780e81502003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame004_links_0000 (interval_append _ 64 128 129 record005_frame004_links_0064 record005_frame004_links_0128))
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x26c996619665493a2988a1e85a1182de2771d9755d3741cd729c8715c26fdbc6d9b36c1a8695a267d815e9765b96958d3a4d1314b52b4a125489204751a45d144390b421003f4fa3dcd533ccc320c630cc02f4bb2e0b52c8af2a4a628c9b26095248912408f2388d2308a2248821c7d1c45f1444c12c4a1244811c46114440e02a0942408c220842007c1e074150400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame005_links_0000 (interval_append _ 64 128 129 record005_frame005_links_0064 record005_frame005_links_0128))
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb20b06afaad6ac7ab79c19a399496f9609518a888687686384b8378248108007f77ea7d47c079678176e7407297126fc6135fe5f35d75cb5bc52750e5014f04e14d34c44b34a449b49048247745944a43d41b40d3fc3ee34d33131f30b2fa2ea2d82c72b72ad2a12932862652552462232132011f01e21d51cd1c41b51a818717816b1570bf09407106205d05c05b05a05905805705605503902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame006_links_0000 (interval_append _ 64 128 129 record005_frame006_links_0064 record005_frame006_links_0128))
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
def record005_frame007_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x5c8b796ced2d9ab2d4027a4f09b935e6748d9051f63bc708d51962ec578a713a23c418690ba14c1a82903603b4d682ce594b2062eadd5429d526a314327d4e69ad33a614b69592223b4688950f2184266e0d39a2328638c317e2ea5b8b41622ba55ca213d26a49490119228438841031fe3e47a0e81c43746b0a51061a43005d0b816c2d0590b015c2b0550720a8128240460881082003e0780e81502003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record005_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record005) (record005.maps 7)
      (record005.inverseMaps 7) record005_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame007_links_0000 (interval_append _ 64 128 129 record005_frame007_links_0064 record005_frame007_links_0128))
theorem record005_frame007_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 7 :=
  of_group record005 7 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record005_frame007_indices record005_frame007_graph record005_frame007_links
def record005_frame008_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x65f64f6456346276195825735665555485404df4cd4c24b64ab4a049748c48548047847046645544843e42841e41540d37a36836234a3413382d72c32bb2ae2a129728f28427d27827026625f24a24023621e21520d2051bf1b71b01a91a419d19618f18918418017a17316615e15714b14313d13913312c12712311d1161070ff0f90f30b208806b05c05705605505405305205105004f03902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record005_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record005) (record005.maps 8)
      (record005.inverseMaps 8) record005_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame008_links_0000 (interval_append _ 64 128 129 record005_frame008_links_0064 record005_frame008_links_0128))
theorem record005_frame008_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 8 :=
  of_group record005 8 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record005_frame008_indices record005_frame008_graph record005_frame008_links
def record005_frame009_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0868.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0868.count (({ width := 9, code := 0x1188ac4e1f0d85c1202ff7dbe5eeef75ba9d0e773395c4e06f375b6da6bb59aad06733194c661b057abb5cac55aac552a550a752289409f4ea7132984ba49208e4621d0682401fcfc7d3d1e0ec75399c8de6e369a0cc6431184c05f2f174b85a2c960ae502611076381b8d86a34198c862301608c401f0f074381b0d06430130803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record005_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record005) (record005.maps 9)
      (record005.inverseMaps 9) record005_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame009_links_0000 (interval_append _ 64 128 129 record005_frame009_links_0064 record005_frame009_links_0128))
theorem record005_frame009_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 9 :=
  of_group record005 9 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0868
    Papers.RationalityTen.SharedFrameCatalogue.group0868_facts record005_frame009_indices record005_frame009_graph record005_frame009_links
def record005_frame010_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc0f5faafb9796bb45cf29fd4d0a6051d289142295949b24b123090147523511848b044f22350f6871424a0d103e7f23ee1f18f5e6883359984c886323109628adc5652ab9514a6c52828c94209f24ea26d93489624a224a11bc8be4502200e306d83621a88cf46523171830bd05c62d31610ae0528281137891c46822210707f43dc1e00e8870c3721980c305d82cc0c904a01c40c405d02e016c0b405902c015c0ac05501c80a804a024011808804202000f807803a015008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record005_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 10)
      (record005.inverseMaps 10) record005_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame010_links_0000 (interval_append _ 64 128 129 record005_frame010_links_0064 record005_frame010_links_0128))
theorem record005_frame010_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 10 :=
  of_group record005 10 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame010_indices record005_frame010_graph record005_frame010_links
def record005_frame011_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x69b68868166f6646555c25b45a959758957d53052351e51851250a5014fa4f34ec4e64df4da4ce4c64be4ae4a749f4983f73e43dd3cb3bd3b034332f32b32331a30e3042f92f12e92e22da2d42bf2b42aa29128727c2702021f41ed1e51dc1cf1c51bb1b21aa1a519d19618117416b15314713d13212912211b11510e1090fd0f70f10eb0ae08806f06005b05a05905805705605505405303902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record005_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 11)
      (record005.inverseMaps 11) record005_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame011_links_0000 (interval_append _ 64 128 129 record005_frame011_links_0064 record005_frame011_links_0128))
theorem record005_frame011_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 11 :=
  of_group record005 11 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record005_frame011_indices record005_frame011_graph record005_frame011_links
def record005_frame012_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6e06d56cf6b76aa69e5e45d35ce5ba5af5a253d52a52551b5105054f84ee4e84df4d94ce4c94b24a749a48347946d4623a839b3943803723683012f22eb2e12d62c82bf2b42ad2a229d29428f27826a25f24923c2322281d01bf1b91b51af1a81a019819018817f17717016615f15714814013713012d12812211c1161101081010f90f30b409006f06005b05a05905805705605505405303902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record005_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record005) (record005.maps 12)
      (record005.inverseMaps 12) record005_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame012_links_0000 (interval_append _ 64 128 129 record005_frame012_links_0064 record005_frame012_links_0128))
theorem record005_frame012_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 12 :=
  of_group record005 12 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record005_frame012_indices record005_frame012_graph record005_frame012_links
def record005_frame013_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1003.count (({ width := 9, code := 0x14ca4d1e87419fcce612e954a24d198b452251187c36170983c1607017ebedf2f2783b9d8e16f371b0d66a31d88c2602fd7abb5cadd6ab358abd56a953a813c9c4d239168943a190882401f8f87a3c1d8e4703719cca6330980be5e2e970b6592c15cac4f27128823c1d8e872381b8d86a34190a4482311084401f0f07438150803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record005_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record005) (record005.maps 13)
      (record005.inverseMaps 13) record005_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame013_links_0000 (interval_append _ 64 128 129 record005_frame013_links_0064 record005_frame013_links_0128))
theorem record005_frame013_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 13 :=
  of_group record005 13 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1003
    Papers.RationalityTen.SharedFrameCatalogue.group1003_facts record005_frame013_indices record005_frame013_graph record005_frame013_links
def record005_frame014_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1004.count (({ width := 9, code := 0x13398cc2592a93c662f16894421b007f3f5f6f97bbd1e2ef773b5d8eb73b95c6dd6db65aecb64b2188c25fac960af56aad52a651a85409f4f27532974aa3d1a8b449f8f87b3c9dcea72379b4d86b351a4ca633096cb2572a950a652289409e4d2612c9443210f87234198c86230178b85a2c15094401f0f074381b0d06430150803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record005_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 14)
      (record005.inverseMaps 14) record005_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame014_links_0000 (interval_append _ 64 128 129 record005_frame014_links_0064 record005_frame014_links_0128))
theorem record005_frame014_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 14 :=
  of_group record005 14 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1004
    Papers.RationalityTen.SharedFrameCatalogue.group1004_facts record005_frame014_indices record005_frame014_graph record005_frame014_links
def record005_frame015_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1002.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1002.count (({ width := 8, code := 0xd3d2d1cecccac6c5c4c1bfbdb8b6b5b3b2b0afaeacabaaa9a8a6a4a39f9e9d9b98979693918f8a888785848281807e7d7c7b7a78767571706f6d696766646361605f5d5c5b5a59575554504f4e4c4b4a49484746444342413d3c3833302f2e2d2c2b2a292826211e1d1c1b1a1918171613100f0e0d0c0b0a090806050403020100 } : Fields).get c.val)
theorem record005_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 15)
      (record005.inverseMaps 15) record005_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame015_links_0000 (interval_append _ 64 128 129 record005_frame015_links_0064 record005_frame015_links_0128))
theorem record005_frame015_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 15 :=
  of_group record005 15 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1002
    Papers.RationalityTen.SharedFrameCatalogue.group1002_facts record005_frame015_indices record005_frame015_graph record005_frame015_links
def record005_frame016_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x34dd1f44cdb31cb2edb9ee4b66d5b46a6a7a9aa4a89a0a7b9e2769ce719ba6b972549323d8e2338c1fb7ddf57ade6785c06f1ba6c9ac699a066d9965d9564d915fd785c5645855e569304a526479174450b41903400fe3ecf93ace6384d4340cc324c5304bd2e8b62cca527c992445d1644c10c3e0f43c0ec3a0e4380dc360c027088210801f0781d0701b068150400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record005_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record005) (record005.maps 16)
      (record005.inverseMaps 16) record005_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame016_links_0000 (interval_append _ 64 128 129 record005_frame016_links_0064 record005_frame016_links_0128))
theorem record005_frame016_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 16 :=
  of_group record005 16 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record005_frame016_indices record005_frame016_graph record005_frame016_links
def record005_frame017_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0757.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0757.count (({ width := 8, code := 0xf4f2f1efeeede1dfdedcdbdacecac8c5c3c1bfbebdbbbab8b6b3b1afaba9a7a6a09e9d9b9a99908e8d8b8a89888786858483827f7d7b787776756c6a6967666564636261605f5e5b5957545352514f4d4b494745413f3d3c31302c28262524232221201f1e1d1c1a1918171615141312110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0757.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record005) (record005.maps 17) (record005.inverseMaps 17) record005_frame017_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record005) (record005.maps 17) (record005.inverseMaps 17) record005_frame017_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record005) (record005.maps 17) (record005.inverseMaps 17) record005_frame017_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0757.localPairCheck (smallEmbedding record005) (record005.maps 17)
      (record005.inverseMaps 17) record005_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame017_links_0000 (interval_append _ 64 128 129 record005_frame017_links_0064 record005_frame017_links_0128))
theorem record005_frame017_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 17 :=
  of_group record005 17 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0757
    Papers.RationalityTen.SharedFrameCatalogue.group0757_facts record005_frame017_indices record005_frame017_graph record005_frame017_links
def record005_frame018_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0755.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0755.count (({ width := 8, code := 0xa09e9d9b9a9996949391908f8c8a8987868584838281807f7e7c7b7a7877767572706f6d6c6b686665636261605f5e5d5c5b5a585756545352514e4c4b494847464544434241403e3d3c3a3938373635343332312f2e2d2c2b2a2928262524232221201f1e1d1c1a1918171615141312110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0755.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record005) (record005.maps 18) (record005.inverseMaps 18) record005_frame018_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record005) (record005.maps 18) (record005.inverseMaps 18) record005_frame018_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record005) (record005.maps 18) (record005.inverseMaps 18) record005_frame018_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0755.localPairCheck (smallEmbedding record005) (record005.maps 18)
      (record005.inverseMaps 18) record005_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame018_links_0000 (interval_append _ 64 128 129 record005_frame018_links_0064 record005_frame018_links_0128))
theorem record005_frame018_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 18 :=
  of_group record005 18 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0755
    Papers.RationalityTen.SharedFrameCatalogue.group0755_facts record005_frame018_indices record005_frame018_graph record005_frame018_links
def record005_frame019_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0756.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0756.count (({ width := 9, code := 0x13095ca249229043e170781c05fefa7bbd1e4f1773b1d6ea74b9dcce370b79b8d96bb55a8c45faf570b65a2bd56aa53a9548a15027d3c9c4d2652a9448a35188a44a1104803e9ecf2783b1d4e672389bcd6693418cc2602f978ba5b2d160ac54291409c45200e46831180bc5c2d160ac5429128803a1c0d86832180b8582a130803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record005_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record005) (record005.maps 19) (record005.inverseMaps 19) record005_frame019_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record005) (record005.maps 19) (record005.inverseMaps 19) record005_frame019_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record005) (record005.maps 19) (record005.inverseMaps 19) record005_frame019_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record005) (record005.maps 19)
      (record005.inverseMaps 19) record005_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame019_links_0000 (interval_append _ 64 128 129 record005_frame019_links_0064 record005_frame019_links_0128))
theorem record005_frame019_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 19 :=
  of_group record005 19 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0756
    Papers.RationalityTen.SharedFrameCatalogue.group0756_facts record005_frame019_indices record005_frame019_graph record005_frame019_links
def record005_frame020_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x25393e4d91a439021082e0880e017fde4779db75dd2739ca721c6711c2701be6d9b16b1a46859e66d725b96c59561575434fd3d4ed384d5324b92c4a9284992446d1543d0741503400de360d5348cc318c02ecb92dcb52ccb12a4a427c9624c902388b2248721483204791d06f1a84c128450f8390e0370d8350d0330c8310b0230781d0701b0681906017058150400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record005_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record005) (record005.maps 20) (record005.inverseMaps 20) record005_frame020_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record005) (record005.maps 20) (record005.inverseMaps 20) record005_frame020_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record005) (record005.maps 20) (record005.inverseMaps 20) record005_frame020_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record005) (record005.maps 20)
      (record005.inverseMaps 20) record005_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame020_links_0000 (interval_append _ 64 128 129 record005_frame020_links_0064 record005_frame020_links_0128))
theorem record005_frame020_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 20 :=
  of_group record005 20 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record005_frame020_indices record005_frame020_graph record005_frame020_links
def record005_frame021_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0x1369a4ce612f9747e3b1c8cc622f0b83c1606ff7ebedf4f97c3ddecf578bc1deec75ba9d2da6c35da8d36931984c05f2e970b65aad166b258ac158ab5529d4ca5522491c8c452210c84409fcfa7b3c9dce26e35998c8623097cba5b2c95caa4f261248c361a8c05e2d160ac54291409c4c251007c3a1c0d86832180b8582a14078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record005_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record005) (record005.maps 21) (record005.inverseMaps 21) record005_frame021_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record005) (record005.maps 21) (record005.inverseMaps 21) record005_frame021_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record005) (record005.maps 21) (record005.inverseMaps 21) record005_frame021_indices (Fin.ofNat record005.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record005_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record005) (record005.maps 21)
      (record005.inverseMaps 21) record005_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record005_frame021_links_0000 (interval_append _ 64 128 129 record005_frame021_links_0064 record005_frame021_links_0128))
theorem record005_frame021_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 21 :=
  of_group record005 21 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record005_frame021_indices record005_frame021_graph record005_frame021_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (Fin.cases (record005_frame007_supported hcells) (Fin.cases (record005_frame008_supported hcells) (Fin.cases (record005_frame009_supported hcells) (Fin.cases (record005_frame010_supported hcells) (Fin.cases (record005_frame011_supported hcells) (Fin.cases (record005_frame012_supported hcells) (Fin.cases (record005_frame013_supported hcells) (Fin.cases (record005_frame014_supported hcells) (Fin.cases (record005_frame015_supported hcells) (Fin.cases (record005_frame016_supported hcells) (Fin.cases (record005_frame017_supported hcells) (Fin.cases (record005_frame018_supported hcells) (Fin.cases (record005_frame019_supported hcells) (Fin.cases (record005_frame020_supported hcells) (Fin.cases (record005_frame021_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))
#print axioms record005_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292
