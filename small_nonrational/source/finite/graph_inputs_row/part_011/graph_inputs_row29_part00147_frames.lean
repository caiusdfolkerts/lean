module
prelude
public import GraphInputsRow29Part00147Data
public import RawFrameSupport
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xe5c71337d9b84daf6beb53da2ad0165c31e9878bf75e0ae456bab4a58c2ba9560a9c529a8553ae9be4db26a53429954c726012e096a4b1a56d2aa94e4a324e925492448ea45521e90848023d51c08d94479f94fa27243879904bee5c02cb9610acc52a28b93cc9c04d125891d88cc442218908c81a3881a88ca062a2f715d8aa0508271131090840e1f70e9870836819e0a88524272132092047423011208584141f80f507883a81c80dc06b034012008d04601b40d406901900c405802b01480a004602200f007403801700b005002600e0068024010007 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record000_frame001_links_0000 (interval_append _ 64 128 133 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xcb1646b1cd8c2c5b61ab04d7febf85d72de969cb2757cab65588abf54b29d94c0a5b507a77d36898f4c025a52b49484a1249d1e68e5468a2f115c89a44421b107282a40c2014fec7e43ea9ee4ef076639c9b1cd8265932a16d4b0055b2a71524a584f327313209764b224c118c8ac43b217109882639f1bb8d9c6c233e1828bd85b02c915f8a884d825f12308e446221f0e606e033018c0ba85a42ca15f0a384d024011408783f81dc0db068830c12008d04601b40d406901900c405802b01480a004602200f007403801700b005002600e0068024010007 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record000_frame002_links_0000 (interval_append _ 64 128 133 record000_frame002_links_0064 record000_frame002_links_0128))
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xdf06e3b67dadcd5e69734199aacc5651b2398f2c2b5feaf4d73cb8a5adacc55f8ae85632ac5538a6952828994189e34e626892fc96d4ae252126c924488a3bd1968ba454a25510687142f212106682c3ef1d18e6669c34498f8bf25c32cd961cae254229a145ca124fc27212d494e48a23e11bc8c64031e00e4c6f83631978c785fa2ed16e8b0851c27d12e093047822f0fd878c36419d0bb85942b414c09e84c824211408784001ea0e406b834412008d04601b40d406901900c405802b01480a004602200f007403801700b005002600e0068024010007 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record000_frame003_links_0000 (interval_append _ 64 128 133 record000_frame003_links_0064 record000_frame003_links_0128))
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x5dfba770ad85abb47656c1d7dacf562a3538a654928950c9fb3b26d4d59812c64fc909172063dc708d71822844b88b0f61bc2f84f06e05c06800fe1f93ea7c4f69e73ca788e69ca3686c4ca9872f65cab7969abd574aa150a9b51a9d137a5b4a49251ea0e3ec794ef1d33746d4d099831e600b51672aa538a413d23c458841011e83b4740e41b6350668c718c2f45b0af1522943f87c0f6190308600640c41602b0520a01182203c0740e01702c0500980e01a02404007 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record000_frame004_links_0000 (interval_append _ 64 128 133 record000_frame004_links_0064 record000_frame004_links_0128))
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x74f3971c4cdf66e136bda2acfd66eb23189ec3c5fbaf05722b5d5a52ac1530a78513a7a93ae9be4db26a53429954c726012e096a4b1a56d2aa94e4a324e5248918487a40d2008fa475a3811b27e53921c48c8260c2eb165cb1653d29514149e64d125811d88c2442216108c82239d1b38ca06382ce15d8a58508262120881c3e41d30de86d03441570a905082721350968490240118087842c1f80f507803a81ca0dc06b034012a09204682300e406f03501a406403101600a404c023011007803a01c00b805002200e0068024010007 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x66632c591ac73630b16d7febf75ea2e296acb4e593abe55b2ac455fa9814b4a394f6a6f536898f4c025a52b49484a1249d1e68e5468a2f115c89a44421a505480a3fb1f58faa7cb3cd9de0ecc6c732c9954b6a5902b59538a96502279935c9904b224b918c8a243b21490988303ae1c30d9c6c63151828ba05b02bf15089b04b824611b08c44461d90e706a83301940c385d42e21650a9051c24011408603f81e20db068830c12a09204682300e406f03501a406403101600a404c023011007803a01c00b805002200e0068024010007 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x5b4b31576a2d33a0f37e6d4a08ef0c60ec147f6f99f03ce78aed1cc3806ecda5adb5663ec6988af35c8b79662c357ca81472864fa9d538a604908fd17a1a4127f8f51d937e6f0d31a232e638c297b2c2564a493f2704b8869071ea3c8768e019c3085c8b315829c4107c0d019c2f85c0b014c2903a06e0c81882f0520a01302203e0740e0170280440700d0120200380600a00800800 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x5e02e296eab2757aab1d56ca95533a959482a3a4fc270131c97d4ada4a523090347e22850c28314109fc4f1c7423949b8cd60681338193cc4060f2fe97dcb7e58f2b29560a7451028193c89da4a523a114488a4221f08f3c75a39e1be0db469a33e18e0c345982a314609e04d025a12608f845c22010908103b21b70d186443061760b585802a414509d04bc11807a03c81a40b405902b01540a804202080c404402100f007403801a00b8058028013008003c01a00c004802000e0060018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x64fb145816ba25b52ce1648afe5632ac950ca7551b27f93989b84c9256928c91a484a3651888af454224d06e7ef3d81d30e2e6e936c9ad4d0667432498d8bee5c22ca1610ac052e28f93d09c24b224f122490447021690687d23d31d30e446d23571950c5c54e28a13c89a84b624b11d88b443a20d0ff87c83881a70cb061c2f01680ac052827412a08e043c11807a03c81a40b405902b01540a804202080c404402100f007403801a00b8058028013008003c01a00c004802000e0060018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0xec757a1cce2efb79b8d96c35dacd468f3b9bcb63f1b8ac4606f977badc2d365b1572af50a6d2285409f4f6713396cae4f208ec6a3313884361708813f9eef17539dc4dc6ab498cc05eadd68ae55a9d449c4c2511685411f0f273379acce612f1689042208f070371a0cc642a14890401f0e06c34180b85828130803c1a0c048200e06018080200 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0522.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0522.count (({ width := 9, code := 0x7f3edf2f87abc9e2f076bb1d4e974395c4e170375b8da6cb61acd469b459ccc65b2990c56230d80bf5eaf176b95b2d568b1582b95aac55aa550a651279349548a3d1a8842208f8773a9c4dc6b3499cc8612f974b4552993c984923914843f1e8ec622b150a04c2511888421b0d0602c15098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0522.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0522.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0522.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0522.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0522
    Papers.RationalityTen.SharedFrameCatalogue.group0522_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0524.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0524.count (({ width := 9, code := 0xb2d8abd5aaad3e9b4aa250a813f9f4e66731974a24d2491c7e37198c45a250f8641e04fc7d3d9e0ee763add2e46f371b0d2683399ac96331186c15f2ed6cb256aa94ea34f26d2a90472250e84409f8f6783a9c8da6833184be5c2c958a650269287e391c0d46632178b85a25120843e1e0d86832180b85828130803c1a0c048200e06018080200 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0524.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame005_links_0000 record003_frame005_links_0064)
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0524
    Papers.RationalityTen.SharedFrameCatalogue.group0524_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0520.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0520.count (({ width := 9, code := 0xdcedf65add468f459fcf6773396c9e3f198bc3e0b017cbcdd6df69b3d86af54a7d1e89409f4ea733799cc6572892c8e411d8d45a290d83c09fefa78bb1cee26eb69acd36632574b7592b95aa85328d409c4ca59208b44a0d027d3d1dcec73379b0a84e269187e3e1e0ec74311809c401f0e06c34180b85828130803c1a0c048200e06018080200 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame006_links_0000 record003_frame006_links_0064)
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0520
    Papers.RationalityTen.SharedFrameCatalogue.group0520_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x636b07d7b8b66595abc55baab253b298546aa214eda68d2da95b499a3f11d28be455214903e7e93ec9e9ce726eb35418c8bee5bd2d495f8a8452d28093b494e46f21c909c7fe3c81da8e286ec31e1758ad454a273123090046222b10d885040e2010f887a83801b40d6069433e1970c8062830617b0ba05b82ae14b0a184f026c12e0938484234112085841411807a03c81a40b405902b01540a804202080c404402100f007403801a00b8058028013008003c01a00c004802000e0060018008002000 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame007_links_0000 record003_frame007_links_0064)
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6aa68a67665063361c6125fa5e25d65c65c05a358356e56554e53752c51a5144e64c94b24a848a45a43b4264003e13c93bd3a739038637637035333031930e2f92e42db2ca2c429627825a25023921c2172051fd1ec1e51d41cc1bb1b419618a18217c17516c16315b15214914013812711e11811210c1050fe0f90f20eb0e40df08c07a07906905a05905605505404204103102202101e01d01c01a01701601401301000f00d00c009008007006003002001000 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame008_links_0000 record003_frame008_links_0064)
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x8e6378d22a8961d8721884a0f826077fdfa7d1f17b9e6795de771d372dc2701b76a9a3679966458d629856057d5e1745c16c5a16457d5b5615253947501394d52e48d1e4611242906408fc3d0f0380d9358cf330c630cc02ecb52c8ad28c9c2649223888214801ec751c86f1384811c400e8390d8350d02e0b4260801f0701b0681805c16050130400f0340c0240801c0600c0200400 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame009_links_0000 record003_frame009_links_0064)
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
def record003_frame010_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0521.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0521.count (({ width := 9, code := 0xa4d1e8b42a04ea7338994c65d2c94c9e43208fc66311589c3e1b0883c09fafa7c3d5e4ee763a9cce470b7dbada6b351a4ce663258ec4612f978b859ac55eab53a9548a04e269248e46a250e83409f8f6773a9c8da6934190c45e2e164ac52281347a371b0c85c2d158a852231107834190b8582a1409848200f06830160a0401c0c05018080200 } : Fields).get c.val)
theorem record003_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0521.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0521.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0521.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0521.localPairCheck (smallEmbedding record003) (record003.maps 10)
      (record003.inverseMaps 10) record003_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame010_links_0000 record003_frame010_links_0064)
theorem record003_frame010_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 10 :=
  of_group record003 10 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0521
    Papers.RationalityTen.SharedFrameCatalogue.group0521_facts record003_frame010_indices record003_frame010_graph record003_frame010_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (Fin.cases (record003_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x709b5219fcc6d595a9c146c9d94d0a5b52ae8f7473230d0e884440fa028ff47d93e29e98f2a7392fb94f0a044a523690e48463c31d90e3c6803101758b5858c2a514889c84c224612008c445621b10a07ac3b81c90e006ac33e1900c185b42ce14b0a184d825c12108d04482180fe07783a41c407d03801b00ce063030016c0b205502a011407003401780ac050023010807403801a00b8058028013008003801800b004001c00c0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
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
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147
