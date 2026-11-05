module
prelude
public import GraphInputsRow28Part00013Data
public import RawFrameSupport
public import SharedFrameGroups006Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups058Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups065Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc8d63bb1958a0c3c51428494009eb4eba6b92fa96f4b0a549298945498248923691348323fd1ee8f134b19f8cd6656320978cac253d28c13cc9c24d124d11dc8ce454219108c8224021ba0bc859c2a914209c84c422b10407e03ca1c30da06883261560a7852028213a099847822e10a077827812608e04682300f607003581a80d206203081780b805b02d01600ae05602a815008603801980c806202a0148098048023011008003e01e00e807002a014008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd2868733e19c2cca52fa92946ea2450826d926490c473a30115a89a432210906081e3fd9fa4fb07c82959458a064f026e12087fc3d81d98e306f23661980c385f82ea1638ad454829411c88203f41ec0ee875c3a01bb0d6869833c1910c506082f81600ac854829614409e84a024211307b827812608e04682300f607003581a80d206203081780b805b02d01600ae05602a815008603801980c806202a0148098048023011008003e01e00e807002a014008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x32763ec658a30e538a51472895069c52e2564a092523a444768d51922e45289911220350680cd19531e5f4b41622b8554a995028e5049f13a26a4c89712c2283fc7c8f31d83a8738de1b0354688cc192314618b716c2d45a0b31642bc570ac150244438821022003a06a0ca1903185c0b61602b0550a81482885009e138210380660c81882a052098120230440800f81e03a0700a81402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x35769cd21a1b3c574ac555aa653ea353c2724d899531a604ae9452724a48a9091f23c3686acd29a033261cb916c2cc57cae95a2a252ca414427e4f09c13623c424818fd1ec3d0788e81c437c6d8d61a633c668c11802fc5f0bd1782e45c0b61642684788a1122203c86e0d21a0338600be1702d0590b01582a8540a6148218380660c81882a052098120230440800f81e03a0700a81402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x645c838ff1de35b4967ece598b255e29c526a233e276cdf98f2ce52c9a9031ce34c6576cec5d73aa748e21a6b3e654c51863015d8b6d672c2560a954e2994dc8a10da073e27b0ef9cb3786bcd219430e5fcbd9632b8548a393c2624307e8ea18c20c3e87a0f21e0358640c21802f8580ae150290510a01382684c0961281f0360660c81882a052098120230440800f81e03a0700a81402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x49792122a4347f84706e0bc12816ff1eabca77ceb9d439f71ae09bd3736c8d6da9b4d594b115fabb56aa8d3b26c4c294d272444628990e21640e7ecfa1ef394668c81802e25acaf95028c4f89b92b2424648a8fe1f43d4778e91c8344658c415a2083d8770ec1d4368660c4184300590b0154298520a213c2704d09812c1f8360620c0178290500941182204207c0f01d03806c0a81402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x43b86b0c216426768ebdd53a8748e4db6b646aed19a133a650c718ab0d5fabd5772e94d69993125f4b692910a164127dcf89e93b6744e49bf3686b0d21a0304574aa14b27a4e49a12723a464891072043f47c0ed1d43906f8db1b03105f8b614c2083d8760ea1d0358620bc1742e0560aa1482804f09c1302584a0921201e8360640c41802a052098120230440800f81e03a0700a81402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0642.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0642.count (({ width := 9, code := 0xf278bc1dcec73395c8e270375b0d669b419ece64b1d8ac360b017cbc59ac962af56aa94aa350275389b4b2512490472351689419f8f8793b1d4e86f369acd26733190c45d2e16cb4592c154a85328938984a249208e4521908823d1e0e870371b0d06632188c05e2d158a8522512088401f0f070361a0c86028130883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0642.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame008_links_0000 record000_frame008_links_0064)
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0642
    Papers.RationalityTen.SharedFrameCatalogue.group0642_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0643.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0643.count (({ width := 9, code := 0x1128843a190a7e3e9f0f67a3c9d4e873389c2df6d361aed5693419ccc5dae56eb559ac552a752a85409e4ca5d2c9448a3d1a8b431f8f87a3b1d4e66e361acd26632188c05b2d164b0572b14ca4512792c9247231148842200fc7c3c1d8e06c351a0c86230178b85a2b148a04e25120843e1e0e86c34190c05c2a140883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame009_links_0000 record000_frame009_links_0064)
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0643
    Papers.RationalityTen.SharedFrameCatalogue.group0643_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xbed5ee2f1d762b9b52fa92946ca2150727552d694849624011d48d444f21ed0e285e41a207d0107f43301940c8062f30f17a8b2e57b2b29510a6c52827c936c9a44c325112509064712008e6c6f636219e0ca462e2e31610ae054e28113789684921fd0f707803a21c30dc86182ec151088827812608e04682300f607003581a80d206203081780b805b02d01600ae05602a815008603801980c806202a0148098048023011008003e01e00e807002a014008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame010_links_0000 record000_frame010_links_0064)
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
def record000_frame011_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x68067566b6616525a859d59358657a56053752a51e51150a5014ec4df4da4d44c64be4b64b03dc3cf3c73ba3ad38a34b33832b31930e3042e92da2d42cb2b42aa29e29324c20b1fc1ed1db1cf1c51aa19d19618d17416b16015512912211b11510e1090f70f10e50cb09008708208108007706e06906806706005f05c05a05905805605505405305204303803303203102a02902602402302202001f01e01d01c01501401100f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record000_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record000) (record000.maps 11)
      (record000.inverseMaps 11) record000_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame011_links_0000 record000_frame011_links_0064)
theorem record000_frame011_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 11 :=
  of_group record000 11 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record000_frame011_indices record000_frame011_graph record000_frame011_links
def record000_frame012_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6c06b36a769b5cd5c05b65ac59f57d54553252550f5054f84df4ce4c94bf4a749a48e48539338637c36f3653433092fa2eb2d52c82bf2a229428f28526a25f25424b2091d91c81b91ae1a81a018817717016b15f15714e14a12d12812211c1161101010f90ee0d509808f08a08908807906e06906806706005f05c05a05905805605505405305204303803303203102a02902602402302202001f01e01d01c01501401100f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record000_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 12) (record000.inverseMaps 12) record000_frame012_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record000) (record000.maps 12)
      (record000.inverseMaps 12) record000_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame012_links_0000 record000_frame012_links_0064)
theorem record000_frame012_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 12 :=
  of_group record000 12 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record000_frame012_indices record000_frame012_graph record000_frame012_links
def record000_frame013_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x3fe7eefc9f73e771ae1dc137c6ecdbda8347680cd99932d63ec618930d608bf97caf449e92922a414788b1039fc3ee7a0f29df39c710e09b835a69cd119d300558a814526c4c49591e234450869001f43d8790df1b4354688cc18e2fc5e0b414c1e43a0700de1b8340620be1782e85a0b21582a0530a41402784e09a1301e83405e0b81682804e090110210400780e81c0360680a81402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record000_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 13) (record000.inverseMaps 13) record000_frame013_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 13)
      (record000.inverseMaps 13) record000_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame013_links_0000 record000_frame013_links_0064)
theorem record000_frame013_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 13 :=
  of_group record000 13 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record000_frame013_indices record000_frame013_graph record000_frame013_links
def record000_frame014_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0547.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0547.count (({ width := 7, code := 0x7cf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0547.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0547.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0547.localPairCheck (smallEmbedding record000) (record000.maps 14) (record000.inverseMaps 14) record000_frame014_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0547.localPairCheck (smallEmbedding record000) (record000.maps 14)
      (record000.inverseMaps 14) record000_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame014_links_0000 record000_frame014_links_0064)
theorem record000_frame014_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 14 :=
  of_group record000 14 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0547
    Papers.RationalityTen.SharedFrameCatalogue.group0547_facts record000_frame014_indices record000_frame014_graph record000_frame014_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (Fin.cases (record000_frame011_supported hcells) (Fin.cases (record000_frame012_supported hcells) (Fin.cases (record000_frame013_supported hcells) (Fin.cases (record000_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x3559a12d0167d33d19dab7c5582a71510a78533284128893048e24311f48ee473a3811b28d2465a2d915e8a84509c9cce465e32598e4c505d228e94249ec4e4269931c9804b925912b094a49024492088f840318c8c0c5de2da1638ae455229914509e84d623c116887441c1d60e306d834e1970c4056429413a095825012608e04682300e207003581a80d206203081700b605a02c81600ae05602a815007203801980c806202a0148090046022010808003e01e00e807002a014007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame001_links_0000 (interval_append _ 64 128 131 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x358191ac79632b141878afb51428514009eb4eba6b92c29594a9253128a93e49ba4c125292248da4191fe8f84789dd4d2c6803359958c825e328c14109e64e126892f895849a24411dc8ce43221190488043741548a54508272131093c47a22b10c88203f01c30da068c3261560a7852028213a099847822e110085025012608e04682300e207003581a80d206203081700b605a02c81600ae05602a815007203801980c806202a0148090046022010808003e01e00e807002a014007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame002_links_0000 (interval_append _ 64 128 131 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1108.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1108.count (({ width := 9, code := 0x4ce512591c8a411c88c3a190b84c19f6f87b3d5e6f1783bddced763a5d0e773385acd368b419ccb602f576ba5c2d96ab459ac962ae56ab156a74e2652e964a249229047a391a8a44a210e8441a0902803f9f0f67a3c9b8da6833998bc5d2c15cac4f271249047231148843211047238198c8622a148904622108803e1e0e8702a14078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame003_links_0000 (interval_append _ 64 128 131 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1108
    Papers.RationalityTen.SharedFrameCatalogue.group1108_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x38a1a50d1067c3385994b3f52fa93146ea2450826d91ce8d346022b513488843b21910a48424181fecfd27d93e4182ca5651828193c09b84821d98e7c7183791b30d5068433018f0c385f82c715a8a945282390f607903ba1d70e807243841bb0da06b434c1910c5060c2f81600ac854829614409e84a024211a089825012608e04682300e207003581a80d206203081700b605a02c81600ae05602a815007203801980c806202a0148090046022010808003e01e00e807002a014007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame004_links_0000 (interval_append _ 64 128 131 record001_frame004_links_0064 record001_frame004_links_0128))
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xe49abb4f690d0d9e2f5574ac955aa653ea35362684ca98d3025d4b495d2a25149c9152123f4787bcda1ac34a680cc9872cc588af95d2b455caa15129c52ca413f2784e49b11e1fa3e47b0f41e23b8758e81ca3886f8d61a6340668c11802fc5f0bd1782e45c0b716c2404788a1122203786e0d21a0338600be1682c8580ae1582a8540a61481c8380660c81882a052090118220420800f81e03a0700a81401e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame005_links_0000 (interval_append _ 64 128 131 record001_frame005_links_0064 record001_frame005_links_0128))
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1107.count (({ width := 9, code := 0x4ce512591c8a411c88c3a190b84c19f6f87b3d5e6f1783bddced763a5d0e773385acd368b419ccb602f576ba5c2d96ab459ac962ae56ab156a74e2652e964a249229047a391a8a44a210e8441a0902803f9f0f67a3c9b8da6833998bc5d2c15cac4f271249047231148843211047238198c8622a148904622108803e1e0e8702a14078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame006_links_0000 (interval_append _ 64 128 131 record001_frame006_links_0064 record001_frame006_links_0128))
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1107
    Papers.RationalityTen.SharedFrameCatalogue.group1107_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0652.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0652.count (({ width := 8, code := 0x8281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0652.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0652.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0652.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0652.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0652.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame007_links_0000 (interval_append _ 64 128 131 record001_frame007_links_0064 record001_frame007_links_0128))
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0652
    Papers.RationalityTen.SharedFrameCatalogue.group0652_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x132a5049b93124a4644a823026013fe7ecf81cfb9671ce1dbeb766deda5b235e6b2d119e336662b654c28f50e9fd3b2624528850d21341c821009fb3ee7c4f59d539c720e199a2cc58cb015d2b054ca69482864fc9d12a2444708c1001f63dc790ed1ce358678c918a1f83e8780ee1d8310610b816c2d0570ac1442804f09c1342604b0941241b0350600bc1702a052090118220420800f81e03a0700a81401e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame008_links_0000 (interval_append _ 64 128 131 record001_frame008_links_0064 record001_frame008_links_0128))
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0559.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0559.count (({ width := 8, code := 0xcdcac8c6c5c4c2bfbdbbbab9b8b4b2b0afaeadacaaa9a8a6a3a2a19f9996949291908f8b89878685848381807f7d7a797876716d6b69686766656362615f5c5b5a58535251504f4e4b4a49484241403f3e3d3c3b3a3936353231302f2e2d2c2b2a292827262522211e1d1c1b1a1918171613120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0559.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame009_links_0000 (interval_append _ 64 128 131 record001_frame009_links_0064 record001_frame009_links_0128))
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0559
    Papers.RationalityTen.SharedFrameCatalogue.group0559_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0257.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0257.count (({ width := 9, code := 0x3b5d6ea74ba1cee571b89c2e06fb75b6d96bb55a6d167b3596c963afd7abb5cabd58aa5429948a351285409f4f27134984b251248c452210c803f9f8fa7c3d9e4ee75399c4de6933994c65c2d160ac5429138984a240d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame010_links_0000 (interval_append _ 64 128 131 record001_frame010_links_0064 record001_frame010_links_0128))
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0257
    Papers.RationalityTen.SharedFrameCatalogue.group0257_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0148.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0148.count (({ width := 9, code := 0x3e5eef579bc5deee76bb1d6ea74b9dcae370b7dbada6bb51a2ce65b1182be5dacd62af56aad52a853a994aa451a813a9a4ba51228a43a11027a3c9e0ee763a9cce26f369acd26531984be5a2c158a852281309448230d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0148.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame011_links_0000 (interval_append _ 64 128 131 record001_frame011_links_0064 record001_frame011_links_0128))
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0148
    Papers.RationalityTen.SharedFrameCatalogue.group0148_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0125.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0125.count (({ width := 8, code := 0x8281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0125.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0125.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0125.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0125.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0125.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record001_frame012_links_0000 (interval_append _ 64 128 131 record001_frame012_links_0064 record001_frame012_links_0128))
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0125
    Papers.RationalityTen.SharedFrameCatalogue.group0125_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x5c42b99544a9b4c325912a6917483234d1628a0432214d08883d41b1df4eb07313699ab8d0e65132198f4af256c2af9544a8653529114189f04ec26f93489884b625412548f246b23291808b64561bf0d3c66031f1858bf855c28f13f09a84ba22a111887042a1e00db86882d01550a2845c2100da06901e40f006f03701740b805b02c015c0ac043020810007203701b009804a024011808404001f00f004c024010007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x8b71221f432802fede33bc762e89ce39872ae45c6b8970adfdbab6e6cad7dac30e5f2bc972aaf5549bd3325d49a92122a4247c8e91b23245a88d0ea1441c820f29d43866b8ce193314610ba96f2ce580ab94f28c4b89291c22c44c879081fe3e4768e61ae338648b413825c348680c818c310550a814c2885009e1381c8380680cc1902504808c1082003e0780a8130240400780e01a0300580a0120200300500800c00800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5ceaca9604adb50fa82d23c8fa473a2a512c88843b21910a4842418206cfee7e53e31ed4f4a6692fb1738b4e4eb26b8fa878c3b31ba8d886a83421980c7861c2fc1738b0c56229214089c446422410b08043e61ec0f207783921c20dd86d035a1a60cc05e82e616c0b285802b21520a5851027a134093047c2340fd06d03540f207803881bc0dc05d02e016c0b205802b815808204001c80dc06c025012008c04202000f807802a013009004001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x16d2b465912bad588ab053b29913fa9da4db25fd2b094448523e11868b5457228113289238b1bdcdae6a334099c8c6e6262e09688b0454e29614749c44d124e923c91047b23a91bc7d43bc1c98d5c65831916c0b145722a914c8a284f426b12608743c81d60e306d834e1970c405a427410107b83c01d20e206d83500e206f03701b00d606a03101800be05d02e016c07203701b00d006603201500a004e025012008c02a013009004001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x18f0bae5862ac15369864b2254d27a92d48da34d1628a044521e90d084441ea0d905e7583571944c7a55f2a194d4a46518285134896c4a824b122c8fa46022d91588a23a91b68d7c69e33f1980c7c5fc2ee1660af855c29e14789f84ba24d11888a844621c10a878036e1a20c685f02d4147085034813609103d81e00e206e02f81740b805b02d01600ae05602a810c08003901b009c04a024011808804001f00f007402a012008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x198abc8581292141691e47d239d1a28c1456a19108483040e2034ff67c63da9e94f266942e714509ae3ea1e30ecc73a38d1bc8cc061c2fc1740b6458e29214089c44be22410788204021fa0f987b03bc1d70e487083761b40d686983301910c085e82e616c0b2854828813d09a84bc25011907b035413609103d81e00e206e02f81740b805b02d01600ae05602a810c08003901b009c04a024011808804001f00f007402a012008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6b266f62b5f45e456d55554a53d5305234f94e34da4c94bd4b249248c4874804444063d23c235834833e33332d3223032f22ed2de2d72cf2b72b32af2aa26624523e23923022621b2091fd1ea1e41de1d51c91c41ab1a518f18a18618117a15f14613a12d11f1130fb0cd0a208b08507106f06a06805b05905805705605405305205104103e03903602702502402302202001f01e01d01501201101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x206beb78ee81c73606aed45a5347680cb99231e62ac4584af75e0bb173ac353c9e533a3745689d0f218424800fa9f33d4794f09ce392714e01a1320634c39822f65c8b315f2a8534a41432764d494120228440859072063d8768e61c0364688c51502343e0790d81a8328620a81482885009e1342604b0940fc1e03706a09c128240460881001f03c0740a8120220400780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd1e6883425a02cfb67a33b55d6ac45582a71512a7853325fd2b094449824752188fa477239d1c08d9469232d17a8b6457a2a0d466813391978c986393141538a5851d28493dc9c84d326393009724b2256129492e49024492086ae32c18c8c0c5e02da1638ae455229914509e84d624c11e08b443a1d60e306d834e1970c405a42b214a09d025011e08e04682300e206c03581a80d206202e81700b605a02c81600ae05602a815007203401980c806202a0128090046022010808003e01e00e807002a010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame001_links_0000 (interval_append _ 64 128 137 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcc9651b2358f2c6662830f14c8a3e51428514029eb4eba5d92d09614aca54d29894549f24dd260929491246d21a90647fa3e0da66ac34b1a00cd8656320953ca5651828213d09c24d125f12b093448823b919c88643221190485c02bc1548a5450a272131093c47a22b10c88203f01d40e186d03461560a7852028213a099849423c117088025011e08e04682300e206c03581a80d206202e81700b605a02c81600ae05602a815007203401980c806202a0128090046022010808003e01e00e807002a010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame002_links_0000 (interval_append _ 64 128 137 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1108.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1108.count (({ width := 9, code := 0x12d954a24b24914822d1388c3a1b0b84c01fafb7c3ddeaf378bc1deee76bb1d4e97439db6d86b34da4d06731584c05eaf174b85b2d568b3592c55eae56ab1429e4e26530964a249229047a391a8b45225108441a0902803f9f4f87b3d1b8d26833998bc592c15cac4f251249047231148843211047234198c8622a128904622108803e1e0e8702a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame003_links_0000 (interval_append _ 64 128 137 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1108
    Papers.RationalityTen.SharedFrameCatalogue.group1108_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd706a034a1a20cf9670b32953aa7452fa931470a2450824791f48e7469a30515a89a44421d90c885242120c101a7fb3f49f64ad25402959460a084f026e0fa878c3b31cf8e346f23661aa0d0866031e1870bf05b22c715a8a944021f30f607903bc1d70e807243841bb0da06b434c1980c886283061600ac854829614409e84bc25012108d025011e08e04682300e206c03581a80d206202e81700b605a02c81600ae05602a815007203401980c806202a0128090046022010808003e01e00e807002a010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame004_links_0000 (interval_append _ 64 128 137 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x36a6bad5da7b49686cf166ac0574ac9562a653e9d537a6c4d099931a604ba9692ba544a2939242454848fce39ba3686b0d31a03325bcb49662c4580ae95a2ae550a894e296520a113f2784e4831001fa3e47b8f41e23b8758e81ca3886f8d91ac34c680c11802fc5f0bd1782e85c8b816e2404588a1122203786a0d21a0338600b61682c8580ae1582a8540a61481c8340660c81882a04a090118220420800f81e03a0700a81001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame005_links_0000 (interval_append _ 64 128 137 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1107.count (({ width := 9, code := 0x12d954a24b24914822d1388c3a1b0b84c01fafb7c3ddeaf378bc1deee76bb1d4e97439db6d86b34da4d06731584c05eaf174b85b2d568b3592c55eae56ab1429e4e26530964a249229047a391a8b45225108441a0902803f9f4f87b3d1b8d26833998bc592c15cac4f251249047231148843211047234198c8622a128904622108803e1e0e8702a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame006_links_0000 (interval_append _ 64 128 137 record006_frame006_links_0064 record006_frame006_links_0128))
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1107
    Papers.RationalityTen.SharedFrameCatalogue.group1107_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb1fb03af7ae8ad3ac4ab49c09a099198196c95d94e8a888687686384b8378248108007f77ea7d47c079678176e7586125fb5f05e15d45c85b952750e5014f04e14d34c44b34a449b49048247745944a43d42b34d33131f30b2fa2ea2d82c72b72ad2a12932862652552462341e21d51cd1c41b51a818717816b15709408f08e08d08c07106c06b06a06906205d05c05b05a05905805705605505403903403303203102a02502402302202102001f01e01d01c01501000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame007_links_0000 (interval_append _ 64 128 137 record006_frame007_links_0064 record006_frame007_links_0128))
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
def record006_frame008_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x72e72271e71971270c70765463d63562961d6106085a959458c57e57256a55d55254b54554053b53652952351d51643942241940d4013f73ee38036a36335434934033532932231c31731130c3002fa2f42ed25123d23222521920c1fc1f21e91e21d81d01c71b41a919f19115e15514e14413b13511f11710b0fd08c08908808708606f06a06906806706005b05a05905805705605505405305203803303203103002a02502402302202102001f01e01d01c01501000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record006_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record006) (record006.maps 8)
      (record006.inverseMaps 8) record006_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame008_links_0000 (interval_append _ 64 128 137 record006_frame008_links_0064 record006_frame008_links_0128))
theorem record006_frame008_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 8 :=
  of_group record006 8 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record006_frame008_indices record006_frame008_graph record006_frame008_links
def record006_frame009_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x49892123244c838f91de12c1881f02601bf97e8efdd8baa746e69c9389702df1bbb706d4d91ad35369ed1d69ac457eadd57aa453a9b92f25b4a49252223d46c8c51622543c869072084087f0cf99632262cc217c2ec5c0b51652be560a89472804ec9a911218418800f81e439c708dc1ac2083e87c0f61e8328610c017c2f0590a814c290510a013c2704d09812c1b8320620c01782904a090118220420800f81e03a0700a81001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record006_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record006) (record006.maps 9)
      (record006.inverseMaps 9) record006_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame009_links_0000 (interval_append _ 64 128 137 record006_frame009_links_0064 record006_frame009_links_0128))
theorem record006_frame009_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 9 :=
  of_group record006 9 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record006_frame009_indices record006_frame009_graph record006_frame009_links
def record006_frame010_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0868.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0868.count (({ width := 9, code := 0x1178a44a210e8642607007f3f1f4f87abbdd6ea7439dcce571381bcdd6db69aed66ab4d8ac2602f978ba5bac55aac552a550a752289409f4ea7132984ba550e8341200fe7e3e9e8f0763a9cce46f371b4d6613017cbc5d2e168b2582b93094492411c8842209007e3b1c0dc6c351a0cc6431180bc582a148a04e231007c3c1d0e06c34190c05c2610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record006_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0868.localPairCheck (smallEmbedding record006) (record006.maps 10)
      (record006.inverseMaps 10) record006_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame010_links_0000 (interval_append _ 64 128 137 record006_frame010_links_0064 record006_frame010_links_0128))
theorem record006_frame010_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 10 :=
  of_group record006 10 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0868
    Papers.RationalityTen.SharedFrameCatalogue.group0868_facts record006_frame010_indices record006_frame010_graph record006_frame010_links
def record006_frame011_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc0c5f92fb57bcbc85d8ae6d4f8a6552fa93146ea21507256526c92c48c24051d48d446122c113c88d43da1c509283440fa024d0a6683301948c8262f30f1628adc5652ab9514a6c52828c94209f24ea26d93489624a224a121071836c1b10d4467a32918b8c185e82e31698b0857029414089bc4b61fd0f707803a21c30dc866030c1760b3025011e08e04682300e206c03581a80d206202e81700b605a02c81600ae05602a815007203401980c806202a0128090046022010808003e01e00e807002a010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record006_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 11)
      (record006.inverseMaps 11) record006_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame011_links_0000 (interval_append _ 64 128 137 record006_frame011_links_0064 record006_frame011_links_0128))
theorem record006_frame011_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 11 :=
  of_group record006 11 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame011_indices record006_frame011_graph record006_frame011_links
def record006_frame012_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x77f77477076b76575e75768967567166465464b63f5d15be5b65a959959058557b57456d56655f55954d54653f53842e41640f4023f23e63db36134d34233532531930e3062ff2f82f12ea2e42d82d12ca2c422420c2041f41ea1de1d41cb1c31bc1b51ae1a819718f18617c14b14313c13512e12811710d1070fc09208d08c08b08a07106c06b06a06906205d05c05b05a05905805705605505403903403303203102a02502402302202102001f01e01d01c01501000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record006_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record006) (record006.maps 12) (record006.inverseMaps 12) record006_frame012_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record006) (record006.maps 12) (record006.inverseMaps 12) record006_frame012_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record006) (record006.maps 12) (record006.inverseMaps 12) record006_frame012_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record006) (record006.maps 12)
      (record006.inverseMaps 12) record006_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame012_links_0000 (interval_append _ 64 128 137 record006_frame012_links_0064 record006_frame012_links_0128))
theorem record006_frame012_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 12 :=
  of_group record006 12 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record006_frame012_indices record006_frame012_graph record006_frame012_links
def record006_frame013_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0998.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0998.count (({ width := 9, code := 0x10783416090381401f0f77b3d5e8f378ba5cee57238dc2df6eb69b0d66a3499ece663257abb5cae16eb559ab558ab552a550a651a813c9c4d2612a944923d0a8441a0902803f1ecf0763a1c8e06d361a8ce612f170b4582b14ca450269047c3d1e0ec72361a8d06632188c05e2e168b0562a148a04e261289046210f074381b0d06430170b0542610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record006_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0998.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record006) (record006.maps 13) (record006.inverseMaps 13) record006_frame013_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record006) (record006.maps 13) (record006.inverseMaps 13) record006_frame013_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record006) (record006.maps 13) (record006.inverseMaps 13) record006_frame013_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0998.localPairCheck (smallEmbedding record006) (record006.maps 13)
      (record006.inverseMaps 13) record006_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame013_links_0000 (interval_append _ 64 128 137 record006_frame013_links_0064 record006_frame013_links_0128))
theorem record006_frame013_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 13 :=
  of_group record006 13 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0998
    Papers.RationalityTen.SharedFrameCatalogue.group0998_facts record006_frame013_indices record006_frame013_graph record006_frame013_links
def record006_frame014_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x34cd1b43cef35cc32bbb2e6b8edeb62d4b42a6a7a9aa4a89a0a7b9e2769ce719ba6b97254932427e9f67d1ef7a9e5781c06f1ba6c9ac699a066d9965d9564d915fd785c5684c1294991e45d1142d0640d003f8fb3e4eb398e1364c5304bd2e8b62cca527c992445915053148511304711845110430f83d0f03b0e8390e0370d8350c02b0a8290a027088210801f0781d0701b068190541003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record006_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record006) (record006.maps 14) (record006.inverseMaps 14) record006_frame014_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record006) (record006.maps 14) (record006.inverseMaps 14) record006_frame014_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record006) (record006.maps 14) (record006.inverseMaps 14) record006_frame014_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record006) (record006.maps 14)
      (record006.inverseMaps 14) record006_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame014_links_0000 (interval_append _ 64 128 137 record006_frame014_links_0064 record006_frame014_links_0128))
theorem record006_frame014_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 14 :=
  of_group record006 14 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record006_frame014_indices record006_frame014_graph record006_frame014_links
def record006_frame015_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0752.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0752.count (({ width := 9, code := 0xfb7cbe1eef5793c1c6e17037db8db6c3459ccd663258ec66230980bf5eaf174b85b2d154a9542994aa350275389b4ca612a944923d1c8c45a29108742a0cf87b3d1e0ec75399c0de6d359a8d26732990c45c2d164b0562a94ca24f2711082401f8f878391c0dc6c34188c05e2e168b0562a148a04e241188842200e870361a0c8602e160a8502610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record006_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record006) (record006.maps 15) (record006.inverseMaps 15) record006_frame015_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record006) (record006.maps 15) (record006.inverseMaps 15) record006_frame015_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record006) (record006.maps 15) (record006.inverseMaps 15) record006_frame015_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record006) (record006.maps 15)
      (record006.inverseMaps 15) record006_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame015_links_0000 (interval_append _ 64 128 137 record006_frame015_links_0064 record006_frame015_links_0128))
theorem record006_frame015_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 15 :=
  of_group record006 15 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0752
    Papers.RationalityTen.SharedFrameCatalogue.group0752_facts record006_frame015_indices record006_frame015_graph record006_frame015_links
def record006_frame016_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0756.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0756.count (({ width := 9, code := 0x12f9549e4b2390c7e1d0a8341205007f3e9eef4793c5dcec75ba9d2e77338dc2de6e36d86be5e2e56eb559abd56aa53a9548a15027d3c9c4d2652a9448a410882401f4f6793c1d8ea73391c4de6b349a0cc5e2e96cb4582b150a450271007e3e1e8f072381b8d86a34188c05e2e168b0562a148a04a241188842200e870361a0c8602e160a8502610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record006_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record006) (record006.maps 16) (record006.inverseMaps 16) record006_frame016_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record006) (record006.maps 16) (record006.inverseMaps 16) record006_frame016_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record006) (record006.maps 16) (record006.inverseMaps 16) record006_frame016_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record006) (record006.maps 16)
      (record006.inverseMaps 16) record006_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame016_links_0000 (interval_append _ 64 128 137 record006_frame016_links_0064 record006_frame016_links_0128))
theorem record006_frame016_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 16 :=
  of_group record006 16 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0756
    Papers.RationalityTen.SharedFrameCatalogue.group0756_facts record006_frame016_indices record006_frame016_graph record006_frame016_links
def record006_frame017_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0781.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0781.count (({ width := 8, code := 0x8887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0781.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0781.localPairCheck (smallEmbedding record006) (record006.maps 17) (record006.inverseMaps 17) record006_frame017_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0781.localPairCheck (smallEmbedding record006) (record006.maps 17) (record006.inverseMaps 17) record006_frame017_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0781.localPairCheck (smallEmbedding record006) (record006.maps 17) (record006.inverseMaps 17) record006_frame017_indices (Fin.ofNat record006.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record006_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0781.localPairCheck (smallEmbedding record006) (record006.maps 17)
      (record006.inverseMaps 17) record006_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record006_frame017_links_0000 (interval_append _ 64 128 137 record006_frame017_links_0064 record006_frame017_links_0128))
theorem record006_frame017_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 17 :=
  of_group record006 17 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0781
    Papers.RationalityTen.SharedFrameCatalogue.group0781_facts record006_frame017_indices record006_frame017_graph record006_frame017_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (Fin.cases (record006_frame008_supported hcells) (Fin.cases (record006_frame009_supported hcells) (Fin.cases (record006_frame010_supported hcells) (Fin.cases (record006_frame011_supported hcells) (Fin.cases (record006_frame012_supported hcells) (Fin.cases (record006_frame013_supported hcells) (Fin.cases (record006_frame014_supported hcells) (Fin.cases (record006_frame015_supported hcells) (Fin.cases (record006_frame016_supported hcells) (Fin.cases (record006_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x71cb5e59e2cea59129c54bc9b6482a3c916a8ae3bd1b5cd886b43519a44d0267232f9930b0456f2af9538a7852c28e94289ee48f24412048f647523791a47262d51610ae455229914509e84d625b12608644141fc0f707803ac1c60db069c32e1880bc05a426c12708c842c1fa0f707803a41c40db05802bc13809b03781b80c005f020810006e03601a80d006603201880a004e0260128090046022009804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0xb5da29b4aa2cb6552888435ecf3763a9d2e873395c8e370b7db4d96c359aad469b459eb458abd5cac55aa9509046a3116894421d0c84411f4f87a3c9e0ee763a1cce471379b4d06732990c66130178ba5c2b154a04f229107439160ac5228138984a2411884401f0f074381b09848180b050241006028100602 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0xde6d72f94c45c2db68a85366d339448a431f8ec72371a8c45a150782405fefd7dbe5ead367b3598ca64b2184a751a813a9a4c259289247215088240a00fe7d3d9e8f2783b1d0d86b349a0ce6532188c2602c15ca451239187439160ac5228138984a2411884401f0f074381b09848180b050241006028100602 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x61ba74930897d4bb25bd2d09614ad254d29893e49ba4c125292248da45121a90647b23bd1d08e146d18f0ae85612a794f4a5651828293d09c24be2561268910477233915488643220810007de3df1e78c145e42e01670af055229614289c849e23d11588644101f80f307503861a10c886002e01600ab053c29014109d04cc25812508f034413609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x662a82d28c93248f24311f48e746a230515a88843b21910a4842418207d01a7fb3eb9f18f6a7a53c9935c8243fe1f50f6078c3b31d00e346f23541a10cc063c30e17e0bac5b22c71518a4850227112f883c4102010fd07cc3d81e50ef075c3921c20dd86d035a1a60cf86603221810bd05cc2d81650b005642a414b0a204f426c12f094035413609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x66ea693da784ea9c937a6c4d299931a5d4b495d2a25149c92d2424547a8e91ba34462650ba9722de5b0b49662c6580ae9572a8544a714b290514a113f26e4d09892e256430849062064007e8fa1ee3d0770eb1d0394710df1b83646b0ce196320628c21823005f8be17a2f05d8ba1722b44b88d0ec1b02e85c0b61682c8580ae1582a8540a61001b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa078bf84583782a81c8097f77e07cf7bf79b79078076f76075073b7277136eb6d96c66b36a055d4fa4ef4e44da4cc4bd4ac49e49047546d4604524444364254154043e43d63c53b63a632d3203133052f52e72d92cd2be2a029628627526725a2492392282071f81e71d91cb1c21ba1ae1a01911831731651560b409508b07606c05d05c05b05a05905805705605505405304003602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6305474f24ec4e24de4d24cb4bf4b14aa49548f48347846c46545944a43c42441740e4053f930e2b92b12ac2a229c29228527a27125c25324a23d23522c21e2112031e81df1d51cc1c018b18718117c17717116c16616115715414f14914313d13813212d12311d11611110e10c10a1051000fb0f60f00ea0e50a908b08307006705805705605505405305205105004f04e03f03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xaaf9498c38b18a889888687686484b8378108007f77ea7d47c07ac7967817567407297126fc5b454053052751c50e5014f14e14d34b34a449b49048247746945944a42941b40d3fc3ee36b35834d34133131f30c2fa2ea2c72b72ad2a12932862752652552322232132011f01e21d51cd1c41b51a81981871780bf09909107806e05f05e05d05c05b05a05905805705605504003602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6145394ed4e54df4d64cd4c24b74ab4a048c48548047847046645c45544843142841e41540d3312e62dd2d72ce2c32bb2af2a129728427d27827026625f25424a24022921e21520d2051cb1c51bf1bc1b71b01aa1a419d18f18918418017a17316c16615e15114b14313d13913312c12712311d11610f1070ff0b208f08506f06805905805705605505405305205105004f03d03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame007_links_0000 record008_frame007_links_0064)
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x9042602ff7ebedf2f77abcde2ed763add4e97439dcce571b89c2e06fb2180be5e2e970b65a2c960ac55aa952a853a994aa451285409f4f2411c8c452210c8541a04f87a3c1d8e872381b4d46431180bc5d2d964ae55299449e4c248dc6c35188c05e2e168b0562a148a04e2612884401f0f074381b0d06430170b0542210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame008_links_0000 record008_frame008_links_0064)
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x5a6a6cd25e91847fa3b11b68c745aa29112087542ea1190648204079ff8fd87db3df1ea4f2077d3b596d0a7652728914089e84e726b93249784a524992048e246422b912487842f20b901c7ea3e71ed8d4067432418a8c185ee2e816c8b2856229d14509e04da260129091c47422210887fc3e41e50eb071836a1a80ce064030a1790b6832013609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame009_links_0000 record008_frame009_links_0064)
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5754c048647f47847046846145845044943d43743042942241c41540e4083fb3f43ed3e73e032b2e62d92cf2c82c22bb2b02a829f29028927e27627126c26525e25724723d2342302291e11d41ca1c11b91b01a71a119a18b18417916f16816115b15615114213812f12a12311c1161101091040fe0f80f30ed0b109008707406b05c05b05a05905805705605505405305204003602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame010_links_0000 record008_frame010_links_0064)
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
def record008_frame011_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1047.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1047.count (({ width := 9, code := 0x98c762d1488c3a190a84c1e0b0380bf9f6f97bbd9e8f2773add0e77334996c96330d82bf5f2f174b85b2cd60ae562ad52a751a813a9c4da51248f46229108742a0d027f3e1e4ee753a1c8e06c34998ca6431988c2602f978ba5c2d94ca24f259247c3d1e0ec74391c0dc6c351a0c860251208c44211007c3c1d0e06c24110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record008) (record008.maps 11) (record008.inverseMaps 11) record008_frame011_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record008) (record008.maps 11)
      (record008.inverseMaps 11) record008_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame011_links_0000 record008_frame011_links_0064)
theorem record008_frame011_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 11 :=
  of_group record008 11 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1047
    Papers.RationalityTen.SharedFrameCatalogue.group1047_facts record008_frame011_indices record008_frame011_graph record008_frame011_links
def record008_frame012_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xad33824cc8c90d1f6394688c316e28c3a85909a0ec1180f001fcbf07bef39dfbb374ac556fad2592b0d5e2b355caa151a9250ea013c2704cc9812c2544888d91522042a780ea1cb38c700dc1b335c6a4cc98e30c600be1742dc5a0b29572965009c13024e46c8990f20e4047e8f61e42443e8770d0180298520a21402784e09a1302584a0920f01a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 12) (record008.inverseMaps 12) record008_frame012_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record008) (record008.maps 12)
      (record008.inverseMaps 12) record008_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame012_links_0000 record008_frame012_links_0064)
theorem record008_frame012_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 12 :=
  of_group record008 12 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record008_frame012_indices record008_frame012_graph record008_frame012_links
def record008_frame013_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0822.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0822.count (({ width := 9, code := 0x843e9e4f1783bddaeb753a1cee471b89c2df6eb71b4d96b34da0ce662f96cb55a2cd62af572b156a853a994aa350a813c9d4d25d2892482210e8642a0d02803f1f4f4793c1dcea73391c0de6c34998c86230980be5e2e970b65a2c93c9a4b23110763a1c8e06e361a8d06632188b8582311084401f0f074381b0d06424110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0822.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 13) (record008.inverseMaps 13) record008_frame013_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (smallEmbedding record008) (record008.maps 13)
      (record008.inverseMaps 13) record008_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame013_links_0000 record008_frame013_links_0064)
theorem record008_frame013_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 13 :=
  of_group record008 13 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0822
    Papers.RationalityTen.SharedFrameCatalogue.group0822_facts record008_frame013_indices record008_frame013_graph record008_frame013_links
def record008_frame014_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0xce5dee16db559ac55ead55aa54ba4d1e89419f4ee713597cb2532792be1e2ee75b9dc6df6db5da6cd65b258cc3602f574b758ab552a651a5d2a9348a39168842a08fc7d3e1ecf2773a9cce26e361a8d0663218cc4612f974b6592b8e870371b0d46833190c4602f170b4582b150a45022108803e1e0e870361a0c8602210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 14) (record008.inverseMaps 14) record008_frame014_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record008) (record008.maps 14)
      (record008.inverseMaps 14) record008_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame014_links_0000 record008_frame014_links_0064)
theorem record008_frame014_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 14 :=
  of_group record008 14 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record008_frame014_indices record008_frame014_graph record008_frame014_links
def record008_frame015_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0349.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0349.count (({ width := 7, code := 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record008_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0349.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0349.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0349.localPairCheck (smallEmbedding record008) (record008.maps 15) (record008.inverseMaps 15) record008_frame015_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0349.localPairCheck (smallEmbedding record008) (record008.maps 15)
      (record008.inverseMaps 15) record008_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame015_links_0000 record008_frame015_links_0064)
theorem record008_frame015_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 15 :=
  of_group record008 15 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0349
    Papers.RationalityTen.SharedFrameCatalogue.group0349_facts record008_frame015_indices record008_frame015_graph record008_frame015_links
def record008_frame016_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0431.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0431.count (({ width := 7, code := 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record008_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0431.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0431.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0431.localPairCheck (smallEmbedding record008) (record008.maps 16) (record008.inverseMaps 16) record008_frame016_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0431.localPairCheck (smallEmbedding record008) (record008.maps 16)
      (record008.inverseMaps 16) record008_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame016_links_0000 record008_frame016_links_0064)
theorem record008_frame016_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 16 :=
  of_group record008 16 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0431
    Papers.RationalityTen.SharedFrameCatalogue.group0431_facts record008_frame016_indices record008_frame016_graph record008_frame016_links
def record008_frame017_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0290.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0290.count (({ width := 7, code := 0xfffbefcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record008_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0290.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0290.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0290.localPairCheck (smallEmbedding record008) (record008.maps 17) (record008.inverseMaps 17) record008_frame017_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0290.localPairCheck (smallEmbedding record008) (record008.maps 17)
      (record008.inverseMaps 17) record008_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame017_links_0000 record008_frame017_links_0064)
theorem record008_frame017_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 17 :=
  of_group record008 17 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0290
    Papers.RationalityTen.SharedFrameCatalogue.group0290_facts record008_frame017_indices record008_frame017_graph record008_frame017_links
def record008_frame018_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x63c2a6d3549984c325d92c89534a024b52368f7472a34d1868b145022350f4868425a11107a83641798f4af256c2af9544a865352931460a144ec26f93489884b6254126491647d23291808b64562288db46be34f19f8cc063e30e17f0bb85982be1570a7851e27e136897449a231115088c43821510307c83c01cc0db868831c17c0b5034813609103c01b80be05e02e81700b605a02c81600ae05602a810006c0270130094048023011008404001f00f0074024011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 18) (record008.inverseMaps 18) record008_frame018_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 18)
      (record008.inverseMaps 18) record008_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame018_links_0000 record008_frame018_links_0064)
theorem record008_frame018_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 18 :=
  of_group record008 18 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame018_indices record008_frame018_graph record008_frame018_links
def record008_frame019_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xa8b27a31c5c8a913a244428770d21641e82f03e04c037fafd9f7be77b6f5de9bcf796ca56c2d0592b0d5f2bb566aa551290512a093d2754e099d2e2534808e51a22f452758e79c83806ecdb1ad344664c297d2ec5c0b59682c0558a79402724d0979292464708a90f2124087e0f51dc298430800de1942b0550a814c290510a013c2704d0980fc1b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 19) (record008.inverseMaps 19) record008_frame019_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record008) (record008.maps 19)
      (record008.inverseMaps 19) record008_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame019_links_0000 record008_frame019_links_0064)
theorem record008_frame019_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 19 :=
  of_group record008 19 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record008_frame019_indices record008_frame019_graph record008_frame019_links
def record008_frame020_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0xcf36369251ca274227fcf89d938e6d4c49792ce53c9d92d226404768c316a2a450894d797aaed5c8b61672c7574ac553a8f50e9f939a6a4c695d272454648ad12a21436770ea9ce38c700dc1b0352688c918b3085f0bb16e2cc57cac14a28c5089f13a26a4bc9592523c4608910c20e2b84a08d0ea1b02e85c0b61682c8580ae1582a8540a60fc1b02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 20) (record008.inverseMaps 20) record008_frame020_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record008) (record008.maps 20)
      (record008.inverseMaps 20) record008_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame020_links_0000 record008_frame020_links_0064)
theorem record008_frame020_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 20 :=
  of_group record008 20 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record008_frame020_indices record008_frame020_graph record008_frame020_links
def record008_frame021_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1096.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1096.count (({ width := 9, code := 0x7bb95bede6e36db2d76b351a4d067b3598ca6431d8ac360b017ebe5eaad4aa4512853e9d4e26930964aa4d249047235168943a190a84419f4f87a3c9dcea74391c0dc6d359a8d0663298cc25f2f174b85b2d164b0572b154a85329130964a23114763a1c8e06e361a8d06632188bc5c241188842200f8783a1c0d86824110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1096.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 21) (record008.inverseMaps 21) record008_frame021_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1096.localPairCheck (smallEmbedding record008) (record008.maps 21)
      (record008.inverseMaps 21) record008_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame021_links_0000 record008_frame021_links_0064)
theorem record008_frame021_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 21 :=
  of_group record008 21 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1096
    Papers.RationalityTen.SharedFrameCatalogue.group1096_facts record008_frame021_indices record008_frame021_graph record008_frame021_links
def record008_frame022_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1097.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1097.count (({ width := 9, code := 0x84bdddced75ba5cee572389c0de6eb6db2d76ab51a4d06733598cb652e15eae562a950a652a8d429f4f27134984b255269147a391a8c45a09027f3e9ecf2783b1d0e471379b4d66934198c86230980be5e2e970b65a2c960ae562a93c9c4d249207a3c1d8e872381b8d86a34198c460251208c44211007c3c1d0e06c24110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 22) (record008.inverseMaps 22) record008_frame022_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record008) (record008.maps 22)
      (record008.inverseMaps 22) record008_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame022_links_0000 record008_frame022_links_0064)
theorem record008_frame022_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 22 :=
  of_group record008 22 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1097
    Papers.RationalityTen.SharedFrameCatalogue.group1097_facts record008_frame022_indices record008_frame022_graph record008_frame022_links
def record008_frame023_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc69646a0d38a5d49a8d511a093e676cd599f31e5dcb394b26e48c818d1192304598a4e8daa34d688cf99a32a63cc55862f85e6bb1712db59cb0d5e2b0536a614aa905168c114220436849039fd3e47b0ec1d239670cde1af34a678ca17e2f45d8b79692c6570a91472784c49291a21826c4087b0d21882a8540a61482885009e1382684c0960f01a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 23) (record008.inverseMaps 23) record008_frame023_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record008) (record008.maps 23)
      (record008.inverseMaps 23) record008_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame023_links_0000 record008_frame023_links_0064)
theorem record008_frame023_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 23 :=
  of_group record008 23 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record008_frame023_indices record008_frame023_graph record008_frame023_links
def record008_frame024_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x84ae8db8b6d6ccd91adb5769ed1da133365aca19131c62ac3982afd5daba1722e05ba96913a2143685907a093fe7e0f89e33ba76ce99d1392700dd9b434667ccd997328588ae9592a8540a594527c4e49812d24e48c8e919226434838fc1ee3d4798f11da3a8720df1b6360690cb188248400790d2180298520a21402784e09a1302584a0920e81a02704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 24) (record008.inverseMaps 24) record008_frame024_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 24) (record008.inverseMaps 24) record008_frame024_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record008) (record008.maps 24)
      (record008.inverseMaps 24) record008_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame024_links_0000 record008_frame024_links_0064)
theorem record008_frame024_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 24 :=
  of_group record008 24 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record008_frame024_indices record008_frame024_graph record008_frame024_links
def record008_frame025_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0642.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0642.count (({ width := 9, code := 0x75b7db4d86bb59a8d3693459ecc6532590c762b1184c15eaed74b95c2b14ea55228d42a04fa7938994ba592a94492451e8e452210e8642a00fc7d3e1e8f2783b9d4e470379b8da6b351a0ce6330980be5e2e970b65a2c960ae562a93c9a4b23110763a1c8e06e361a8d06632188b8582311084401f0f074381b0d06424110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0642.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record008) (record008.maps 25) (record008.inverseMaps 25) record008_frame025_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record008) (record008.maps 25) (record008.inverseMaps 25) record008_frame025_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record008) (record008.maps 25)
      (record008.inverseMaps 25) record008_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame025_links_0000 record008_frame025_links_0064)
theorem record008_frame025_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 25 :=
  of_group record008 25 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0642
    Papers.RationalityTen.SharedFrameCatalogue.group0642_facts record008_frame025_indices record008_frame025_graph record008_frame025_links
def record008_frame026_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0641.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0641.count (({ width := 8, code := 0x979392908f8e8d8c8b8a89878584838281807f7e7c7b7a7978747371706f6e6d6c6b6a68666564636261605f5d5c5b5a5958565554535251504f4d4b4a4948474645444241403f3e3d3c3b3a393837363531302f2e2d2b2a292827262524232221201f1d1c1b1a1918171615141311100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record008_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0641.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0641.localPairCheck (smallEmbedding record008) (record008.maps 26) (record008.inverseMaps 26) record008_frame026_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0641.localPairCheck (smallEmbedding record008) (record008.maps 26) (record008.inverseMaps 26) record008_frame026_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0641.localPairCheck (smallEmbedding record008) (record008.maps 26)
      (record008.inverseMaps 26) record008_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame026_links_0000 record008_frame026_links_0064)
theorem record008_frame026_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 26 :=
  of_group record008 26 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0641
    Papers.RationalityTen.SharedFrameCatalogue.group0641_facts record008_frame026_indices record008_frame026_graph record008_frame026_links
def record008_frame027_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6b25e457f57256d56255554a54053052350b5034f94ee4e34da4cc4bd4b249a49248c4874803c236435b35835134833e33632d32230f3093032fc2f22ed2e12d72cf2bc2b72b32af2aa24523e23923022621b2122091fd1ea1e41de1d51c91c41b71ab1a518f18a18618117a17216715f15514613a12e11f1130a208b08506f06805b05a05905805705605505405305205103e03602702602502402302202102001f01e01d01201101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 27) (record008.inverseMaps 27) record008_frame027_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 27) (record008.inverseMaps 27) record008_frame027_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 27)
      (record008.inverseMaps 27) record008_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame027_links_0000 record008_frame027_links_0064)
theorem record008_frame027_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 27 :=
  of_group record008 27 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record008_frame027_indices record008_frame027_graph record008_frame027_links
def record008_frame028_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x81ae39b33616c0d6dabb51698d1da0336664cb994b2463cc5d88b095fabdd782ec5ce99d1f23946e8c915a2744086109206406800fd9f53e67b0f29e13ac738e49c5380640c69873045ecb916f2cc57caa14d29050c9d9352604a09011422042c839032023f07b0f21da398708d91a22343e0790d41882a0530a41442804f09c1342604b0940f01a82704c094120230440841001f03c0740901102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 28) (record008.inverseMaps 28) record008_frame028_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 28) (record008.inverseMaps 28) record008_frame028_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record008) (record008.maps 28)
      (record008.inverseMaps 28) record008_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame028_links_0000 record008_frame028_links_0064)
theorem record008_frame028_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 28 :=
  of_group record008 28 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record008_frame028_indices record008_frame028_graph record008_frame028_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (Fin.cases (record008_frame011_supported hcells) (Fin.cases (record008_frame012_supported hcells) (Fin.cases (record008_frame013_supported hcells) (Fin.cases (record008_frame014_supported hcells) (Fin.cases (record008_frame015_supported hcells) (Fin.cases (record008_frame016_supported hcells) (Fin.cases (record008_frame017_supported hcells) (Fin.cases (record008_frame018_supported hcells) (Fin.cases (record008_frame019_supported hcells) (Fin.cases (record008_frame020_supported hcells) (Fin.cases (record008_frame021_supported hcells) (Fin.cases (record008_frame022_supported hcells) (Fin.cases (record008_frame023_supported hcells) (Fin.cases (record008_frame024_supported hcells) (Fin.cases (record008_frame025_supported hcells) (Fin.cases (record008_frame026_supported hcells) (Fin.cases (record008_frame027_supported hcells) (Fin.cases (record008_frame028_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa86a7da75a69a5ca4ea3ca2fa1fa0c93d93292991d9109038f28e58d68c484583782a81c8097f77e07cf7bf7a879b79078076f76075073b7277137005d85cf5c65bc5ae59d58d5805705624fa4ef4e44da4cc4bd4ac49e49048047546d4604524444364254154043f532d3203133052f52e72d92cd2be2ac2a029628627526725a24923922821a1c21ba1ae1a019118317316515614608a08908808708606b06a06906806705c05b05a05905805705605505405305203503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame001_links_0000 (interval_append _ 64 128 155 record009_frame001_links_0064 record009_frame001_links_0128))
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb2eb24b1fb12b03af7ae9ad3ac4ab49d49c59c09b29a099198296c95d94e8c38b18a889888687686484b8378248108007f77ea7d47c07ac79678176e62861a6126085fb5f05e25d45c85b954053052751c50e5014f14e14d34c44b34a449b49048247746945944a43d36b35834d34133131f30c2fa2ea2d82c72b72ad2a12932862752652552461e21d51cd1c41b51a819818717816b09008f08e08d08c06d06c06b06a06905e05d05c05b05a05905805705605505403503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame002_links_0000 (interval_append _ 64 128 155 record009_frame002_links_0064 record009_frame002_links_0128))
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x393e438de2b87e1380df378dd33cce736ccf30cb728c8f1ec6af8bd2f0baee6b86d8b3ec6b02baadab2ab6a9a96a0a6692a363c8e6368ce308b62888a1c861fd7e9f77cdef7ade576dd1729c4705be6e5b56c5ac6959e66557551515394a519414e5314a9244851e469164490e421023f4df36cd734ccf32cc72fcb72c06017c5e1745c13c4e1344c12c461144410c42104400fc3e0f43c0c8310c02f0b8260942408c220842007c1e0741c0441003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame003_links_0000 (interval_append _ 64 128 155 record009_frame003_links_0064 record009_frame003_links_0128))
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30a1834c0c6002fc97dabdf5e42ec5736a9854429f14e2a6552fa93546ea2150725f12d69594a424d9258919480a3a91a88c2458227911a87b438a17d09283440f9a90d2c68533c99a0cc065332098bcc3c5a62cb9628af656e2b29560a8a5362941464a104f9275136c9a44c425892889283ad1cd8e306f636c1b10d4867a32918b8c185e82e31698b085702a814a0a044de1fd0f707803a21c30dc86ac3301860bb024011e08e04682300da06c03581a80d205e02e81700b605a02c81600ae05602a815006a03401980c80620260128090046022010808003e01e00e8070022010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame004_links_0000 (interval_append _ 64 128 155 record009_frame004_links_0064 record009_frame004_links_0128))
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x138e6ecdc9b735a69ccf997322624758d91a23245c8b514a24c4187505604c037fefd1f73e57b4f3de23be76eec1d6ba673ee71cab8c70ac2180afc5f0bc977ae85c0b6568aac546a754d29351ca153da724d299130a594ac94d2624b48c8fd1d1e13ae744e61c23766dcd89ab34a67ccc19231c618c017a2e059caf12d2504848e917220428810fa1e21c8388700de1b82e85c0b61682c85009e1382684c0961282484808e118198320620c01782604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame005_links_0000 (interval_append _ 64 128 155 record009_frame005_links_0064 record009_frame005_links_0128))
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x352d3f4cd2746d0f3ccd730caef2bbeecba6e6b8edfb62d4b42aeaaaa6a8a9ea6a93a26829ee789da739c66e9ae6397254931fe7f1fa7e1f67d1f07a9e5781c4709c06f9bc6e9b36b1a66819b6659765593645885fd785c5384d1304b5294991f45d1142d0640d003f8fb3e4f33ace6384c5304bd2e8b62ccad2949f26455150531485112047118451103f0f83d0f03b0e8390e0370d8350b02b0a8290a023088210801f0781d0701b068190441003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame006_links_0000 (interval_append _ 64 128 155 record009_frame006_links_0064 record009_frame006_links_0128))
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x2278922187a1b862148420c821e7791e1779db761d5749cf731b76d1b16b9ab6a1a367999651926418e6318a6218660d805f55855954549505394b521455092e4b12a4a1264912247d1c46516451124410e43109415013f4d7350d1338cb320c5300bb2d8b22c0ae2b0aa2a0a62889e2688821884208801f87c1dc721b44e1344c12c4a104400fc3e0f4380dc360d4340cc320c4300bc2e0a42809c260942007c1e0741c06c1a0641805c160441003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame007_links_0000 (interval_append _ 64 128 155 record009_frame007_links_0064 record009_frame007_links_0128))
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
def record009_frame008_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x2c1afabaadeb3ac2adaa6a6a8e639825d96a579525193a4b922328ba2a89e238821d8661684e108320a81a04801fe7f1f87d9ad6a9a7695a26819e66d9965d825f97c5e5775d1725c16d5ad69591615755a559545454d52d1243105400f93d0f13a8e5388e1370d934cd0328c8314bf2f4a9294a22749a254932408b2246017c5e1745c1384d1304b1284511043108411003f0f83d0f03b0b02b0a8290a023088210801f0781d0701b068190441003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record009_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record009) (record009.maps 8)
      (record009.inverseMaps 8) record009_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame008_links_0000 (interval_append _ 64 128 155 record009_frame008_links_0064 record009_frame008_links_0128))
theorem record009_frame008_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 8 :=
  of_group record009 8 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record009_frame008_indices record009_frame008_graph record009_frame008_links
def record009_frame009_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0390.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0390.count (({ width := 8, code := 0xc7c5c3c1bfbdbbb9b7b5b3b1afadaba9a7a5a3a1a09f9e9d9c9b9a999897969594939291908f8e8d868482807e7c7a787674737271706f6e6d6c6b6a696867666564636261605a595857565554535251504f4e4d4c4b4a49484741403f3e3d3c3b3a3938363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0390.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0390.localPairCheck (smallEmbedding record009) (record009.maps 9)
      (record009.inverseMaps 9) record009_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame009_links_0000 (interval_append _ 64 128 155 record009_frame009_links_0064 record009_frame009_links_0128))
theorem record009_frame009_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 9 :=
  of_group record009 9 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0390
    Papers.RationalityTen.SharedFrameCatalogue.group0390_facts record009_frame009_indices record009_frame009_graph record009_frame009_links
def record009_frame010_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x32dd960ca9651b27192ac8e643b2018f2ada56a2b3558cabf55c2ac5554aa354e26a93309864bb25912a6940496a46d2148f7472a34d1868b145022350f486842b99ecce866e3339980cb26523259910c7c5792b6157caa254329a9498a3050a27e13b09be4d226212d895049924591f48de36d1af8d3c67e33018f8c385fc2ee16e8b3057c2ae14f0a3c4fc26d12e89344782060f907803981b70d106382f816a0ab824011e08e04682300da06c03581a80d205e02e81700b605a02c81600ae05602a815006a03401980c80620260128090046022010808003e01e00e8070022010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record009_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record009) (record009.maps 10)
      (record009.inverseMaps 10) record009_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame010_links_0000 (interval_append _ 64 128 155 record009_frame010_links_0064 record009_frame010_links_0128))
theorem record009_frame010_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 10 :=
  of_group record009 10 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record009_frame010_indices record009_frame010_graph record009_frame010_links
def record009_frame011_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6dd6da6d76d36cd6c96c46bd6b86b361160d6096045fe5fa5f55ef5ea5e557f57256d56255554a54053052351950b5034f94ee4e34da4cc4bd4b24a53ed3e93e53e03db3d73d33ce3c93c336435b35835134833e33632d32231b30f3093032fc2f22ed2e12d72cf2c624523e23923022621b2122091fd1f41ea1e41de1d51c91c41b71ab1a519917216715f15514613a12e11f11310708408308208108006706606506406305a05905805705605505405305205105003503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record009) (record009.maps 11)
      (record009.inverseMaps 11) record009_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame011_links_0000 (interval_append _ 64 128 155 record009_frame011_links_0064 record009_frame011_links_0128))
theorem record009_frame011_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 11 :=
  of_group record009 11 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record009_frame011_indices record009_frame011_graph record009_frame011_links
def record009_frame012_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0374.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0374.count (({ width := 9, code := 0x5cae16eb65aad166b258ac151a7d369749a3d1687419fcd6652f964a64d239047637178a4461d0b8441604ff7eb95c6e16fb75b6d96bb55a6ca6431988c2602f976b85b2c960ae562a950a651a813c9047a391a8c45a2910864220902803f9f8fa7c3d1e0ec6e361a8d0663218cc25f2e90c8441200fc783b1d0e470361a8d06632188c05e2e168b05228138984a200f8783a1c0d86832180b8582210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record009) (record009.maps 12)
      (record009.inverseMaps 12) record009_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame012_links_0000 (interval_append _ 64 128 155 record009_frame012_links_0064 record009_frame012_links_0128))
theorem record009_frame012_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 12 :=
  of_group record009 12 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0374
    Papers.RationalityTen.SharedFrameCatalogue.group0374_facts record009_frame012_indices record009_frame012_graph record009_frame012_links
def record009_frame013_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x69268b68467e67a67466f66b6656615b25ab5a459d59959458e58a58558053052651b5135094ff4f44ee4e74e24d94cf4c44bb4b54ae4a649c49248b3a83a339e39839338f38a38538137c32b32331931430c3062fd2f72f22ed2e72df2d52ce2c82c32bd2b52af2a922421920c2031fc1f31ea1e31dc1d61cc1c11b41ac1a519e19618f18617e15914e14513d13212711e11310810108a08908808708606b06a06906806705c05b05a05905805705605505405305203503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record009) (record009.maps 13)
      (record009.inverseMaps 13) record009_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame013_links_0000 (interval_append _ 64 128 155 record009_frame013_links_0064 record009_frame013_links_0128))
theorem record009_frame013_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 13 :=
  of_group record009 13 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record009_frame013_indices record009_frame013_graph record009_frame013_links
def record009_frame014_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x10a2134248430720bc1281f02602bc3780ef5dd3b5762eadd43a373cdc9b5b656c0d65aab4d68ed019db36662cad92b20630c4d86b065fea4947a8b510a0d3fa7a4ee9c936a4547e8e11aa3145c8a111a1f4348610a20e40e810ff9fa3ec7c8f6997322624c39822fa5d8b916b2ca584ae95729e524a193e2764d4979112144047c8f31d83986f8d71a22003f87e0fa1f0338660ca1903185a0b21602b8560aa150298520a21401a8340660c81882604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record009) (record009.maps 14)
      (record009.inverseMaps 14) record009_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame014_links_0000 (interval_append _ 64 128 155 record009_frame014_links_0064 record009_frame014_links_0128))
theorem record009_frame014_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 14 :=
  of_group record009 14 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record009_frame014_indices record009_frame014_graph record009_frame014_links
def record009_frame015_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x34b1a4ad1e68bb441a12d0267db3d19dab0f57eabad5b0ac45582a75512a78533268d32297f4b6256128893148ea4311f48ee473a3811b28d2465a31117a8b64579b10d686a33489a04ce465f32618e4c5056f2af9538a7852c28e94289ee4e4269931c9804b925912b094a49e24b924091237f1b50d5c68232c18c8c105e02da1638ae455229914509e84d625b12608f045a1d60e306d834e1970c405e02d21590a5024011e08e04682300da06c03581a80d205e02e81700b605a02c81600ae05602a815006a03401980c80620260128090046022010808003e01e00e8070022010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record009_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 15)
      (record009.inverseMaps 15) record009_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame015_links_0000 (interval_append _ 64 128 155 record009_frame015_links_0064 record009_frame015_links_0128))
theorem record009_frame015_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 15 :=
  of_group record009 15 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record009_frame015_indices record009_frame015_graph record009_frame015_links
def record009_frame016_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78c78577f77a77477076c76575e75769f69468967e67567166565464b63f5e45da5d15c95be5b65aa59959058557b57456d56655f55955454d54653f44343842e42141640f4033f23e63db37636c36135734d34233632531930e3062ff2f82f12ea2e42df2d82d12ca23c23222421a20c2041f51ea1de1d41cb1c31bc1b51ae1a81a119718f18614b14313c13512e12812111710d10708e08d08c08b08a06d06c06b06a06905e05d05c05b05a05905805705605505403503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record009) (record009.maps 16)
      (record009.inverseMaps 16) record009_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame016_links_0000 (interval_append _ 64 128 155 record009_frame016_links_0064 record009_frame016_links_0128))
theorem record009_frame016_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 16 :=
  of_group record009 16 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record009_frame016_indices record009_frame016_graph record009_frame016_links
def record009_frame017_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x68067b67466d66665e6576506486425b05a859a59158857c57156655a55550e5064f84ee4e34d74d04c74bb4b34ac4a64a049a49348c48647f4784723a239738b37d37436a35d35434c3432f32e82dc2cd2c42bc2af2a629c29428d28728127a27426d26726125a2551e81dc1d21c81c01b61ad1a519b19518f18717c17617216e16816315d15812d12511a11210d1071020fe0fa0f608c08b08a08908806b06a06906806705c05b05a05905805705605505405305203403303203103002602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 17) (record009.inverseMaps 17) record009_frame017_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 17) (record009.inverseMaps 17) record009_frame017_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 17) (record009.inverseMaps 17) record009_frame017_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 17)
      (record009.inverseMaps 17) record009_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame017_links_0000 (interval_append _ 64 128 155 record009_frame017_links_0064 record009_frame017_links_0128))
theorem record009_frame017_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 17 :=
  of_group record009 17 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record009_frame017_indices record009_frame017_graph record009_frame017_links
def record009_frame018_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0163.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0163.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0163.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0163.localPairCheck (smallEmbedding record009) (record009.maps 18) (record009.inverseMaps 18) record009_frame018_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0163.localPairCheck (smallEmbedding record009) (record009.maps 18) (record009.inverseMaps 18) record009_frame018_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0163.localPairCheck (smallEmbedding record009) (record009.maps 18) (record009.inverseMaps 18) record009_frame018_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0163.localPairCheck (smallEmbedding record009) (record009.maps 18)
      (record009.inverseMaps 18) record009_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame018_links_0000 (interval_append _ 64 128 155 record009_frame018_links_0064 record009_frame018_links_0128))
theorem record009_frame018_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 18 :=
  of_group record009 18 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0163
    Papers.RationalityTen.SharedFrameCatalogue.group0163_facts record009_frame018_indices record009_frame018_graph record009_frame018_links
def record009_frame019_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0388.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0388.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0388.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0388.localPairCheck (smallEmbedding record009) (record009.maps 19) (record009.inverseMaps 19) record009_frame019_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0388.localPairCheck (smallEmbedding record009) (record009.maps 19) (record009.inverseMaps 19) record009_frame019_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0388.localPairCheck (smallEmbedding record009) (record009.maps 19) (record009.inverseMaps 19) record009_frame019_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0388.localPairCheck (smallEmbedding record009) (record009.maps 19)
      (record009.inverseMaps 19) record009_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame019_links_0000 (interval_append _ 64 128 155 record009_frame019_links_0064 record009_frame019_links_0128))
theorem record009_frame019_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 19 :=
  of_group record009 19 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0388
    Papers.RationalityTen.SharedFrameCatalogue.group0388_facts record009_frame019_indices record009_frame019_graph record009_frame019_links
def record009_frame020_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x26a9a66899e669966498e62986408f2398da338be2b8a2248860f82e08816027f9fa7ddf37c1ec7a1e5789df76dd7751d0735a568d9f671996599163d8c625755cd6f5b1695996157d5c565545494e52d48515404f93b4e1244811c4591243508411003f0f83d0f03a8e6384dc360d4340b82d0b02a8a62849c260942405e1745c16c5a1404f1384d130471184511043108411003f0f83d0b42c0ac2a0a4210801f0781d0701b06819060170441003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record009_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record009) (record009.maps 20) (record009.inverseMaps 20) record009_frame020_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record009) (record009.maps 20) (record009.inverseMaps 20) record009_frame020_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record009) (record009.maps 20) (record009.inverseMaps 20) record009_frame020_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record009) (record009.maps 20)
      (record009.inverseMaps 20) record009_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame020_links_0000 (interval_append _ 64 128 155 record009_frame020_links_0064 record009_frame020_links_0128))
theorem record009_frame020_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 20 :=
  of_group record009 20 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record009_frame020_indices record009_frame020_graph record009_frame020_links
def record009_frame021_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0988.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0988.count (({ width := 9, code := 0x42611078341609038140600f87b3d1e4f0773b5d6e973b89c0de6e369b0d76ab4da2cf66b2d92c762b1184c05f2d968b2582b958aa54a9d4a9f4ea6d32974aa4d24904722d128742a0d027f3f1f0f4753a1cce471381bcdc6c351a0ce6632990c6623097cba562a950a652289409e4d258fc7c3d1e0ec74391c0dc6c351a0cc6431180bc5c2d160ac482311084401c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0988.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record009) (record009.maps 21) (record009.inverseMaps 21) record009_frame021_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record009) (record009.maps 21) (record009.inverseMaps 21) record009_frame021_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record009) (record009.maps 21) (record009.inverseMaps 21) record009_frame021_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0988.localPairCheck (smallEmbedding record009) (record009.maps 21)
      (record009.inverseMaps 21) record009_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame021_links_0000 (interval_append _ 64 128 155 record009_frame021_links_0064 record009_frame021_links_0128))
theorem record009_frame021_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 21 :=
  of_group record009 21 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0988
    Papers.RationalityTen.SharedFrameCatalogue.group0988_facts record009_frame021_indices record009_frame021_graph record009_frame021_links
def record009_frame022_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1034.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1034.count (({ width := 9, code := 0x3c9e2f077bb9daec75ba9d2e57238dc2df6eb6db2d76ab49a2d06733194c86331184c05faf978ba5c2d968b2582b154a85329146a04f27534974aa4d228f4722d128842a0d027f3e9ecf4773a9d0e26f371b4d86b351a0ce663218cc4613017cbc5c2d968b052289409e4e2692c9449238f0763a1c8e06e361a8d06632188c05e2e168b0562a148a04622108803e1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1034.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1034.localPairCheck (smallEmbedding record009) (record009.maps 22) (record009.inverseMaps 22) record009_frame022_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1034.localPairCheck (smallEmbedding record009) (record009.maps 22) (record009.inverseMaps 22) record009_frame022_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1034.localPairCheck (smallEmbedding record009) (record009.maps 22) (record009.inverseMaps 22) record009_frame022_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1034.localPairCheck (smallEmbedding record009) (record009.maps 22)
      (record009.inverseMaps 22) record009_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame022_links_0000 (interval_append _ 64 128 155 record009_frame022_links_0064 record009_frame022_links_0128))
theorem record009_frame022_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 22 :=
  of_group record009 22 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1034
    Papers.RationalityTen.SharedFrameCatalogue.group1034_facts record009_frame022_indices record009_frame022_graph record009_frame022_links
def record009_frame023_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x33b19b6cc965c328d91ac7a6333141878a8753b29914a6a3e51428554029eb4eba6112fa9764b7a5a12c295a4a9a53128a93e49ba4c125292248da45121a90647f9be4dc86d33601ab0d2c6813361958c825742b0953ca7a52b28c14149e84e126892f895849a24411dc8ce45522190c88463051790b8059c2bc1548a5850a272131093c47a22b10c88203f01e60ea070c3681560a7852028213a09984b024a11e08b824011e08e04682300da06c03581a80d205e02e81700b605a02c81600ae05602a815006a03401980c80620260128090046022010808003e01e00e8070022010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record009_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 23) (record009.inverseMaps 23) record009_frame023_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 23) (record009.inverseMaps 23) record009_frame023_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 23) (record009.inverseMaps 23) record009_frame023_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 23)
      (record009.inverseMaps 23) record009_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame023_links_0000 (interval_append _ 64 128 155 record009_frame023_links_0064 record009_frame023_links_0128))
theorem record009_frame023_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 23 :=
  of_group record009 23 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record009_frame023_indices record009_frame023_graph record009_frame023_links
def record009_frame024_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6a76a169868d68568067766c6616525cf5c75bf5ba5b15a859f59458657a53d53753052a52351e51951250a5014fa4f34ec4e64df4da4d54ce4c64be4074013f53ee3e23dc3d23c83ba3ad35434b34333832f32b32431a30e3042f92f12e92e22da2d42cc2bf2b42aa21620b2021fc1f41ed1e61dc1cf1c51bb1b21aa1a519d19618e18117416b12912211b11510e1091040fd0f70f108408308208108006b06a06906806705c05b05a05905805705605505405305203503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 24) (record009.inverseMaps 24) record009_frame024_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 24) (record009.inverseMaps 24) record009_frame024_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 24) (record009.inverseMaps 24) record009_frame024_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record009) (record009.maps 24)
      (record009.inverseMaps 24) record009_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame024_links_0000 (interval_append _ 64 128 155 record009_frame024_links_0064 record009_frame024_links_0128))
theorem record009_frame024_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 24 :=
  of_group record009 24 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record009_frame024_indices record009_frame024_graph record009_frame024_links
def record009_frame025_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x15dab956cacf58eafd58aa3532a34cf997316604bc9712c6554a593f18e2e45489d1222143b8690b212c1e82f03e04c037fafd9f7be77c0d75ac35369cd25a233e670cc5952d85a0b2561abe576acd54aa2536a4144a824f49d5382674b894d249d639e720e01bb36c6b4d119931e614be9762e05acb41602ac53ca4123238454879092043f07a8ee1ce1fc3f07d0f81ec320630c4184300550a814c290510a013c2704d09812c1a8340660c81882604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 25) (record009.inverseMaps 25) record009_frame025_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 25) (record009.inverseMaps 25) record009_frame025_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 25) (record009.inverseMaps 25) record009_frame025_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 25)
      (record009.inverseMaps 25) record009_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame025_links_0000 (interval_append _ 64 128 155 record009_frame025_links_0064 record009_frame025_links_0128))
theorem record009_frame025_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 25 :=
  of_group record009 25 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record009_frame025_indices record009_frame025_graph record009_frame025_links
def record009_frame026_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x12b6544a293925648c899091fa3c418827036034017f6fd5f73ea7c6ed1d7ba7740e61c8b87702dedba36e6d2d85acb5369ad199f33765caed5c2b5560aad52aa0536a5548a5d4b294d2824c4909011da344648b11321f430845052043fa7d8f819d32e640c49822f65d0b69662c256cab9512945149f13c2704d09810f2144187f8f91e43ac728de1b01f43e07b0f41e4330650c818c310570ac1542a0530a41442804f09c1341a8340660c81882604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record009) (record009.maps 26) (record009.inverseMaps 26) record009_frame026_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record009) (record009.maps 26) (record009.inverseMaps 26) record009_frame026_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record009) (record009.maps 26) (record009.inverseMaps 26) record009_frame026_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record009) (record009.maps 26)
      (record009.inverseMaps 26) record009_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame026_links_0000 (interval_append _ 64 128 155 record009_frame026_links_0064 record009_frame026_links_0128))
theorem record009_frame026_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 26 :=
  of_group record009 26 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record009_frame026_indices record009_frame026_graph record009_frame026_links
def record009_frame027_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0274.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0274.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0274.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0274.localPairCheck (smallEmbedding record009) (record009.maps 27) (record009.inverseMaps 27) record009_frame027_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0274.localPairCheck (smallEmbedding record009) (record009.maps 27) (record009.inverseMaps 27) record009_frame027_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0274.localPairCheck (smallEmbedding record009) (record009.maps 27) (record009.inverseMaps 27) record009_frame027_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0274.localPairCheck (smallEmbedding record009) (record009.maps 27)
      (record009.inverseMaps 27) record009_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame027_links_0000 (interval_append _ 64 128 155 record009_frame027_links_0064 record009_frame027_links_0128))
theorem record009_frame027_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 27 :=
  of_group record009 27 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0274
    Papers.RationalityTen.SharedFrameCatalogue.group0274_facts record009_frame027_indices record009_frame027_graph record009_frame027_links
def record009_frame028_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1108.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1108.count (({ width := 9, code := 0x4be5d2d964aa51269248a41188bc5a2b1388c3e1b0b84c0a03007fbf5f6f97bbd5e6f1783bddced763add4e974375b8db6d361acd4693419cc76331588c2602f978ba5c2d96ab459ac962b057ab95aa351285409e4e26930964a249229047a391a8c45a29128441a0902803f9f8fa7c3d9a8d26833998b4592c15cac4b251249047231148843211046a34198c86226128904622108803e1e0e8702210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record009) (record009.maps 28) (record009.inverseMaps 28) record009_frame028_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record009) (record009.maps 28) (record009.inverseMaps 28) record009_frame028_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record009) (record009.maps 28) (record009.inverseMaps 28) record009_frame028_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record009) (record009.maps 28)
      (record009.inverseMaps 28) record009_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame028_links_0000 (interval_append _ 64 128 155 record009_frame028_links_0064 record009_frame028_links_0128))
theorem record009_frame028_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 28 :=
  of_group record009 28 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1108
    Papers.RationalityTen.SharedFrameCatalogue.group1108_facts record009_frame028_indices record009_frame028_graph record009_frame028_links
def record009_frame029_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0x58ac15dad562ad53a853a9742a04f675389b4ce612e95c9647208ec6e331689c461d0b84c1a07017fbf1f2f77a3a5d0e672b91c6e16fb79b8d96c359aad469b459ece663298ec5613017aba5c2d564a651a853c9c4ca5928914723116894421d0c8441204fe773b1d0e672389bcda6c351389a4c259288642209007e381b8d86a34198c86230178b84e2612890461f0f074381b0d06430170b0542210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 29) (record009.inverseMaps 29) record009_frame029_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 29) (record009.inverseMaps 29) record009_frame029_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 29) (record009.inverseMaps 29) record009_frame029_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 29)
      (record009.inverseMaps 29) record009_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame029_links_0000 (interval_append _ 64 128 155 record009_frame029_links_0064 record009_frame029_links_0128))
theorem record009_frame029_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 29 :=
  of_group record009 29 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record009_frame029_indices record009_frame029_graph record009_frame029_links
def record009_frame030_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0808.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0808.count (({ width := 8, code := 0xf7f5f3f1efedebe9e7e6e3e1dfdddbd9d7d5d3d2cfcdcbc9c7c5c3c1bfbebbb9b7b5b3b1afadabaaa3a2a1a09f9e9d9c9b9a999897969594939291908e8c8a88868482807e7d7573716f6d6b696765646261605f5e5d5c5b5a59535251504f4e4d4c4b4a3c3b3a39383635343332302f2e2d2c2b2a29282726232221201f1d1c1b1a1918171615141311100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0808.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0808.localPairCheck (smallEmbedding record009) (record009.maps 30) (record009.inverseMaps 30) record009_frame030_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0808.localPairCheck (smallEmbedding record009) (record009.maps 30) (record009.inverseMaps 30) record009_frame030_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0808.localPairCheck (smallEmbedding record009) (record009.maps 30) (record009.inverseMaps 30) record009_frame030_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0808.localPairCheck (smallEmbedding record009) (record009.maps 30)
      (record009.inverseMaps 30) record009_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame030_links_0000 (interval_append _ 64 128 155 record009_frame030_links_0064 record009_frame030_links_0128))
theorem record009_frame030_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 30 :=
  of_group record009 30 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0808
    Papers.RationalityTen.SharedFrameCatalogue.group0808_facts record009_frame030_indices record009_frame030_graph record009_frame030_links
def record009_frame031_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0x6b355a7d268b419dcd6632b85c1e02fb7bbcddae771b7596c760aed6eb356a9d469d4ba4d1a87419fcf273379a4863f1d8e46e35188b452230782405fefd7dbe5eaf277badd0e671b85bcdb6c351a0bf5e2e96eb5592bd58a8522813a9a4c25928924722d107f3e9ecf4793c1d8e872379409e4e269308a442190882381b8d86a34198c86230178b84e2612890461f0f074381b0d06430170b0542210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 31) (record009.inverseMaps 31) record009_frame031_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 31) (record009.inverseMaps 31) record009_frame031_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 31) (record009.inverseMaps 31) record009_frame031_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 31)
      (record009.inverseMaps 31) record009_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame031_links_0000 (interval_append _ 64 128 155 record009_frame031_links_0064 record009_frame031_links_0128))
theorem record009_frame031_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 31 :=
  of_group record009 31 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record009_frame031_indices record009_frame031_graph record009_frame031_links
def record009_frame032_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0639.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0639.count (({ width := 9, code := 0x65f2d95c9e4b218cc561f0973b95c6df6eb65a2cd63b055ead55aa54aa14da5d1e8942a0d027f3d9dce26d3297c5627108742e130781c0600f4793c1dcec75ba1cae37137dbcdd6db65acd46933d98b55a2cd62af562a950a55127d3a9b4ca5d2c93482391a803f9f4f4783a1c8e26c359208e46229107e3e1e8f076351a0cc6431180bc5c2d160ac4a2411888421e0e870361a0c8602e160a8502210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record009) (record009.maps 32) (record009.inverseMaps 32) record009_frame032_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record009) (record009.maps 32) (record009.inverseMaps 32) record009_frame032_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record009) (record009.maps 32) (record009.inverseMaps 32) record009_frame032_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record009) (record009.maps 32)
      (record009.inverseMaps 32) record009_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame032_links_0000 (interval_append _ 64 128 155 record009_frame032_links_0064 record009_frame032_links_0128))
theorem record009_frame032_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 32 :=
  of_group record009 32 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0639
    Papers.RationalityTen.SharedFrameCatalogue.group0639_facts record009_frame032_indices record009_frame032_graph record009_frame032_links
def record009_frame033_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0774.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0774.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0774.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0774.localPairCheck (smallEmbedding record009) (record009.maps 33) (record009.inverseMaps 33) record009_frame033_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0774.localPairCheck (smallEmbedding record009) (record009.maps 33) (record009.inverseMaps 33) record009_frame033_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame033_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0774.localPairCheck (smallEmbedding record009) (record009.maps 33) (record009.inverseMaps 33) record009_frame033_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0774.localPairCheck (smallEmbedding record009) (record009.maps 33)
      (record009.inverseMaps 33) record009_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame033_links_0000 (interval_append _ 64 128 155 record009_frame033_links_0064 record009_frame033_links_0128))
theorem record009_frame033_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 33 :=
  of_group record009 33 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0774
    Papers.RationalityTen.SharedFrameCatalogue.group0774_facts record009_frame033_indices record009_frame033_graph record009_frame033_links
def record009_frame034_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0332.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0332.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0332.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0332.localPairCheck (smallEmbedding record009) (record009.maps 34) (record009.inverseMaps 34) record009_frame034_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0332.localPairCheck (smallEmbedding record009) (record009.maps 34) (record009.inverseMaps 34) record009_frame034_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame034_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0332.localPairCheck (smallEmbedding record009) (record009.maps 34) (record009.inverseMaps 34) record009_frame034_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0332.localPairCheck (smallEmbedding record009) (record009.maps 34)
      (record009.inverseMaps 34) record009_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame034_links_0000 (interval_append _ 64 128 155 record009_frame034_links_0064 record009_frame034_links_0128))
theorem record009_frame034_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 34 :=
  of_group record009 34 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0332
    Papers.RationalityTen.SharedFrameCatalogue.group0332_facts record009_frame034_indices record009_frame034_graph record009_frame034_links
def record009_frame035_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0922.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0922.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0922.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0922.localPairCheck (smallEmbedding record009) (record009.maps 35) (record009.inverseMaps 35) record009_frame035_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0922.localPairCheck (smallEmbedding record009) (record009.maps 35) (record009.inverseMaps 35) record009_frame035_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame035_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0922.localPairCheck (smallEmbedding record009) (record009.maps 35) (record009.inverseMaps 35) record009_frame035_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0922.localPairCheck (smallEmbedding record009) (record009.maps 35)
      (record009.inverseMaps 35) record009_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame035_links_0000 (interval_append _ 64 128 155 record009_frame035_links_0064 record009_frame035_links_0128))
theorem record009_frame035_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 35 :=
  of_group record009 35 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0922
    Papers.RationalityTen.SharedFrameCatalogue.group0922_facts record009_frame035_indices record009_frame035_graph record009_frame035_links
def record009_frame036_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0923.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0923.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0923.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0923.localPairCheck (smallEmbedding record009) (record009.maps 36) (record009.inverseMaps 36) record009_frame036_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0923.localPairCheck (smallEmbedding record009) (record009.maps 36) (record009.inverseMaps 36) record009_frame036_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame036_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0923.localPairCheck (smallEmbedding record009) (record009.maps 36) (record009.inverseMaps 36) record009_frame036_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0923.localPairCheck (smallEmbedding record009) (record009.maps 36)
      (record009.inverseMaps 36) record009_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame036_links_0000 (interval_append _ 64 128 155 record009_frame036_links_0064 record009_frame036_links_0128))
theorem record009_frame036_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 36 :=
  of_group record009 36 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0923
    Papers.RationalityTen.SharedFrameCatalogue.group0923_facts record009_frame036_indices record009_frame036_graph record009_frame036_links
def record009_frame037_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0715.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0715.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0715.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0715.localPairCheck (smallEmbedding record009) (record009.maps 37) (record009.inverseMaps 37) record009_frame037_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0715.localPairCheck (smallEmbedding record009) (record009.maps 37) (record009.inverseMaps 37) record009_frame037_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame037_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0715.localPairCheck (smallEmbedding record009) (record009.maps 37) (record009.inverseMaps 37) record009_frame037_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0715.localPairCheck (smallEmbedding record009) (record009.maps 37)
      (record009.inverseMaps 37) record009_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame037_links_0000 (interval_append _ 64 128 155 record009_frame037_links_0064 record009_frame037_links_0128))
theorem record009_frame037_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 37 :=
  of_group record009 37 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0715
    Papers.RationalityTen.SharedFrameCatalogue.group0715_facts record009_frame037_indices record009_frame037_graph record009_frame037_links
def record009_frame038_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0848.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0848.count (({ width := 9, code := 0x46a311689c461f0d854220f02803f9f6f97bbd5e4f077badd2e772389c0de6db65b0d569b459ccc653218ac3612ed74b95c2dd6cb559ac962b057ab95aac55aa950a75329144a04ea6d32964a249228843211027f3e9e8f0763a9cce471381bcdc6d359a8d26230980be5e2e970b4592c110864220900783b1d0e47034198c86230178b85a2c158a84a2411888421e0e870361a0c8602e160a8502210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 38) (record009.inverseMaps 38) record009_frame038_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 38) (record009.inverseMaps 38) record009_frame038_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame038_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 38) (record009.inverseMaps 38) record009_frame038_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 38)
      (record009.inverseMaps 38) record009_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame038_links_0000 (interval_append _ 64 128 155 record009_frame038_links_0064 record009_frame038_links_0128))
theorem record009_frame038_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 38 :=
  of_group record009 38 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0848
    Papers.RationalityTen.SharedFrameCatalogue.group0848_facts record009_frame038_indices record009_frame038_graph record009_frame038_links
def record009_frame039_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0984.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0984.count (({ width := 8, code := 0xefedebe9e7e5e3e1dfdddbd9d7d5d3d1cfcdcbc9c7c5c3c1bfbdbbb9b7b5b3b1afadaba9a7a5a3a19b9a999897969594939291908f8e8d8c8b8a8988868482807e7c7a7876746d6b69676563615f5d5b5a5958575655545352514b4a4948474645444342363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0984.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record009) (record009.maps 39) (record009.inverseMaps 39) record009_frame039_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record009) (record009.maps 39) (record009.inverseMaps 39) record009_frame039_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame039_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record009) (record009.maps 39) (record009.inverseMaps 39) record009_frame039_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record009) (record009.maps 39)
      (record009.inverseMaps 39) record009_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame039_links_0000 (interval_append _ 64 128 155 record009_frame039_links_0064 record009_frame039_links_0128))
theorem record009_frame039_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 39 :=
  of_group record009 39 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0984
    Papers.RationalityTen.SharedFrameCatalogue.group0984_facts record009_frame039_indices record009_frame039_graph record009_frame039_links
def record009_frame040_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0546.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0546.count (({ width := 8, code := 0xc2c0bfbebdbcbbb9b8b7b3b2b0afaeadacaba9a8a3a2a19f9e9d9c9a9998979695949291908f8d8c87868584838281807f7e7b797876757372706f6e6d6c6b6a6967666564635f5e5d5c5b5958575655545351504e4c4b4a48474544434241403f3e3d3c373635343331302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0546.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0546.localPairCheck (smallEmbedding record009) (record009.maps 40) (record009.inverseMaps 40) record009_frame040_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0546.localPairCheck (smallEmbedding record009) (record009.maps 40) (record009.inverseMaps 40) record009_frame040_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame040_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0546.localPairCheck (smallEmbedding record009) (record009.maps 40) (record009.inverseMaps 40) record009_frame040_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0546.localPairCheck (smallEmbedding record009) (record009.maps 40)
      (record009.inverseMaps 40) record009_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame040_links_0000 (interval_append _ 64 128 155 record009_frame040_links_0064 record009_frame040_links_0128))
theorem record009_frame040_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 40 :=
  of_group record009 40 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0546
    Papers.RationalityTen.SharedFrameCatalogue.group0546_facts record009_frame040_indices record009_frame040_graph record009_frame040_links
def record009_frame041_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0773.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0773.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0773.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0773.localPairCheck (smallEmbedding record009) (record009.maps 41) (record009.inverseMaps 41) record009_frame041_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0773.localPairCheck (smallEmbedding record009) (record009.maps 41) (record009.inverseMaps 41) record009_frame041_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame041_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0773.localPairCheck (smallEmbedding record009) (record009.maps 41) (record009.inverseMaps 41) record009_frame041_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0773.localPairCheck (smallEmbedding record009) (record009.maps 41)
      (record009.inverseMaps 41) record009_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame041_links_0000 (interval_append _ 64 128 155 record009_frame041_links_0064 record009_frame041_links_0128))
theorem record009_frame041_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 41 :=
  of_group record009 41 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0773
    Papers.RationalityTen.SharedFrameCatalogue.group0773_facts record009_frame041_indices record009_frame041_graph record009_frame041_links
def record009_frame042_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0331.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0331.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0331.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0331.localPairCheck (smallEmbedding record009) (record009.maps 42) (record009.inverseMaps 42) record009_frame042_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0331.localPairCheck (smallEmbedding record009) (record009.maps 42) (record009.inverseMaps 42) record009_frame042_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame042_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0331.localPairCheck (smallEmbedding record009) (record009.maps 42) (record009.inverseMaps 42) record009_frame042_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0331.localPairCheck (smallEmbedding record009) (record009.maps 42)
      (record009.inverseMaps 42) record009_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame042_links_0000 (interval_append _ 64 128 155 record009_frame042_links_0064 record009_frame042_links_0128))
theorem record009_frame042_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 42 :=
  of_group record009 42 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0331
    Papers.RationalityTen.SharedFrameCatalogue.group0331_facts record009_frame042_indices record009_frame042_graph record009_frame042_links
def record009_frame043_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0260.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0260.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0260.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0260.localPairCheck (smallEmbedding record009) (record009.maps 43) (record009.inverseMaps 43) record009_frame043_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0260.localPairCheck (smallEmbedding record009) (record009.maps 43) (record009.inverseMaps 43) record009_frame043_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame043_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0260.localPairCheck (smallEmbedding record009) (record009.maps 43) (record009.inverseMaps 43) record009_frame043_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0260.localPairCheck (smallEmbedding record009) (record009.maps 43)
      (record009.inverseMaps 43) record009_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame043_links_0000 (interval_append _ 64 128 155 record009_frame043_links_0064 record009_frame043_links_0128))
theorem record009_frame043_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 43 :=
  of_group record009 43 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0260
    Papers.RationalityTen.SharedFrameCatalogue.group0260_facts record009_frame043_indices record009_frame043_graph record009_frame043_links
def record009_frame044_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3675b0ed706ac3501a50d1167cb385994ac5558aa75512a7452fa935470a24508251926491e48623e91ce8d4460a2b513488843b21910a4842418207d01a7fb3f49644afa5692aa9500a5651928213c09b84121ff0fa87b03c61d98e8071a3791b30d5068433018f0c385f82eb16c8b1c56a20f10408043f41f30f607943bc1d70e807243841bb0da06b434c19f0cc06443141600ac854829614409e84d825e128090824011e08e04682300da06c03581a80d205e02e81700b605a02c81600ae05602a815006a03401980c80620260128090046022010808003e01e00e8070022010007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record009_frame044_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame044_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 44) (record009.inverseMaps 44) record009_frame044_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame044_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 44) (record009.inverseMaps 44) record009_frame044_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame044_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 44) (record009.inverseMaps 44) record009_frame044_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame044_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 44)
      (record009.inverseMaps 44) record009_frame044_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame044_links_0000 (interval_append _ 64 128 155 record009_frame044_links_0064 record009_frame044_links_0128))
theorem record009_frame044_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 44 :=
  of_group record009 44 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame044_indices record009_frame044_graph record009_frame044_links
def record009_frame045_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x69a69168b68067466a65c64f6436355a059958e58857b57656c55e55754c4f24ec4e24de4d24cb4bf4b14aa49e49548f48347846c46545944a43c43036735e35934d34733d33032831e3132b92b12ac2a229c29228527a27126525c25324a23d23522c21e2112031f718b18718117c17717116c16616115d15715414f14914313d13813212d12910c10a1051000fb0f60f00ea0e50e008208108007f07e06606506406306205705605505405305205105004f04e04d03503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame045_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame045_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 45) (record009.inverseMaps 45) record009_frame045_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame045_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 45) (record009.inverseMaps 45) record009_frame045_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame045_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 45) (record009.inverseMaps 45) record009_frame045_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame045_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record009) (record009.maps 45)
      (record009.inverseMaps 45) record009_frame045_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame045_links_0000 (interval_append _ 64 128 155 record009_frame045_links_0064 record009_frame045_links_0128))
theorem record009_frame045_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 45 :=
  of_group record009 45 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record009_frame045_indices record009_frame045_graph record009_frame045_links
def record009_frame046_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x66966365e65764c64263b63162461758d58558157857056355c55254553d4ed4e54df4d64cd4c24b74ab4a049748c48548047847046645c45544843e38637e37937036535f35434733e3352e62dd2d72ce2c32bb2af2a129728f28427d27827026625f25424a2402361cb1c51bf1bc1b71b01aa1a419d19618f18918418017a17316c16615e15713312c12712311d11610f1070ff0f908408308208108006706606506406305805705605505405305205105004f04e03503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame046_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame046_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 46) (record009.inverseMaps 46) record009_frame046_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame046_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 46) (record009.inverseMaps 46) record009_frame046_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame046_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 46) (record009.inverseMaps 46) record009_frame046_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame046_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record009) (record009.maps 46)
      (record009.inverseMaps 46) record009_frame046_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame046_links_0000 (interval_append _ 64 128 155 record009_frame046_links_0064 record009_frame046_links_0128))
theorem record009_frame046_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 46 :=
  of_group record009 46 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record009_frame046_indices record009_frame046_graph record009_frame046_links
def record009_frame047_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6e86e66de6db6d36ce6c26b46a769b5f15e85e15d85d05cd5c35b75ac59f54d54553d53252a52551c5105054f84ee4e84df4d94ce4c94c04b24a749a3b73ad3a539f39839338937d36f3653133093012fa2f22eb2e22d62c82bf2b42ad2a229d29428f28627826a25f1e11d91d01c81bf1b91b61af1a81a019819018817f17717016c16615f15712d12812211c11611010d1081010f908c08b08a08908806b06a06906806705c05b05a05905805705605505405305203503403303203102602502402302202102001f01e01d01c01101000f00e00d00c00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record009_frame047_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame047_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 47) (record009.inverseMaps 47) record009_frame047_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame047_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 47) (record009.inverseMaps 47) record009_frame047_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame047_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 47) (record009.inverseMaps 47) record009_frame047_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame047_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 47)
      (record009.inverseMaps 47) record009_frame047_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame047_links_0000 (interval_append _ 64 128 155 record009_frame047_links_0064 record009_frame047_links_0128))
theorem record009_frame047_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 47 :=
  of_group record009 47 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record009_frame047_indices record009_frame047_graph record009_frame047_links
def record009_frame048_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0082.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0082.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame048_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0082.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame048_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0082.localPairCheck (smallEmbedding record009) (record009.maps 48) (record009.inverseMaps 48) record009_frame048_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame048_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0082.localPairCheck (smallEmbedding record009) (record009.maps 48) (record009.inverseMaps 48) record009_frame048_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame048_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0082.localPairCheck (smallEmbedding record009) (record009.maps 48) (record009.inverseMaps 48) record009_frame048_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame048_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0082.localPairCheck (smallEmbedding record009) (record009.maps 48)
      (record009.inverseMaps 48) record009_frame048_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame048_links_0000 (interval_append _ 64 128 155 record009_frame048_links_0064 record009_frame048_links_0128))
theorem record009_frame048_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 48 :=
  of_group record009 48 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0082
    Papers.RationalityTen.SharedFrameCatalogue.group0082_facts record009_frame048_indices record009_frame048_graph record009_frame048_links
def record009_frame049_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x102a02c017fafe1fa3f07d8f99f0b9271ce21c2b806f8dddb9b6e6ced059db3766ccc597328644c798db16624c2d83b025fabe97aaef5d4a013da784e49b9352654c49712aa2e44c88d0f21942c84105a064047f8fc9f53e07b0f39e43c4770ec1873025f4bc9722da59cb095b2aa538a614527c4e09912e2564888e0f71e63b4738e21bc3686a0cf1941e83c8780ee1d83005f0bc1742e0530a41442804f09c1342604b094124198320620c01782604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame049_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame049_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record009) (record009.maps 49) (record009.inverseMaps 49) record009_frame049_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame049_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record009) (record009.maps 49) (record009.inverseMaps 49) record009_frame049_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame049_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record009) (record009.maps 49) (record009.inverseMaps 49) record009_frame049_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame049_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record009) (record009.maps 49)
      (record009.inverseMaps 49) record009_frame049_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame049_links_0000 (interval_append _ 64 128 155 record009_frame049_links_0064 record009_frame049_links_0128))
theorem record009_frame049_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 49 :=
  of_group record009 49 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record009_frame049_indices record009_frame049_graph record009_frame049_links
def record009_frame050_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x12ca57cab9512925049c93324a4642884907e0cc1382302a01bfe7ecee9dbbb0756e91cfb9771ee1dbeb766deda5b235e6b2d4da5b44678acd57aa8548a754c2905109fd3b2404788d919a2e4528890da1341c821009fb3ee7c4f59e53ba754e71832fc5e0b916c2cc590b095d2b054ca69482864fc9d1362604a8911001f63dc790ed1ce38c6e8d619e1e83c8780ee1d82f05d0b816c2d0530a41442804f09c1342604b094124190310600bc1702604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame050_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame050_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 50) (record009.inverseMaps 50) record009_frame050_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame050_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 50) (record009.inverseMaps 50) record009_frame050_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame050_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 50) (record009.inverseMaps 50) record009_frame050_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame050_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record009) (record009.maps 50)
      (record009.inverseMaps 50) record009_frame050_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame050_links_0000 (interval_append _ 64 128 155 record009_frame050_links_0064 record009_frame050_links_0128))
theorem record009_frame050_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 50 :=
  of_group record009 50 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record009_frame050_indices record009_frame050_graph record009_frame050_links
def record009_frame051_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0xe79ccb9772ce45c6b8a706dedbbb3d674cd59932c656c9d9031b62cbbd75ae55c4b716bad2598b1960abb56eac5572a9548a854da9551e8e11922c4508951021c428839051e93c477cee9db3ae748e61c63866f4db1b135c6b0d31a233a658c914928a4fc9d9362624bc949232404748d115220430839031fc3e47a8dc1b0344670ca18c3085e8b81661d83a8740e61c82f85e0ba1702d8510a013c2704d09812c2504909011c1883005e0b81682604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame051_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame051_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 51) (record009.inverseMaps 51) record009_frame051_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame051_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 51) (record009.inverseMaps 51) record009_frame051_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame051_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 51) (record009.inverseMaps 51) record009_frame051_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame051_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record009) (record009.maps 51)
      (record009.inverseMaps 51) record009_frame051_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame051_links_0000 (interval_append _ 64 128 155 record009_frame051_links_0064 record009_frame051_links_0128))
theorem record009_frame051_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 51 :=
  of_group record009 51 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record009_frame051_indices record009_frame051_graph record009_frame051_links
def record009_frame052_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1045.count (({ width := 11, code := 0xf1de23c277eeeddabb375eea5d33686c8d75ab350694d119eb37668c35843015f4bcd76ae75beb5d69acb592b0d5dab7560aad5329e5328ed1b22f4508810c213418819009da3ac73ce41c13766d8d81aa34c67cce99731e628c117e2f45ccb693a2704d49992f2564a0921202384688c11321c42c831011fc3e47a0d81ac344660c91882fc5e0b71641b83686c0d61a82c8580ae1582a84d09812c2504909011c2304508810c190310600bc1702604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame052_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame052_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record009) (record009.maps 52) (record009.inverseMaps 52) record009_frame052_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame052_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record009) (record009.maps 52) (record009.inverseMaps 52) record009_frame052_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame052_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record009) (record009.maps 52) (record009.inverseMaps 52) record009_frame052_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame052_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record009) (record009.maps 52)
      (record009.inverseMaps 52) record009_frame052_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame052_links_0000 (interval_append _ 64 128 155 record009_frame052_links_0064 record009_frame052_links_0128))
theorem record009_frame052_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 52 :=
  of_group record009 52 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1045
    Papers.RationalityTen.SharedFrameCatalogue.group1045_facts record009_frame052_indices record009_frame052_graph record009_frame052_links
def record009_frame053_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0387.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0387.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame053_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0387.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame053_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0387.localPairCheck (smallEmbedding record009) (record009.maps 53) (record009.inverseMaps 53) record009_frame053_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame053_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0387.localPairCheck (smallEmbedding record009) (record009.maps 53) (record009.inverseMaps 53) record009_frame053_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame053_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0387.localPairCheck (smallEmbedding record009) (record009.maps 53) (record009.inverseMaps 53) record009_frame053_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame053_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0387.localPairCheck (smallEmbedding record009) (record009.maps 53)
      (record009.inverseMaps 53) record009_frame053_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame053_links_0000 (interval_append _ 64 128 155 record009_frame053_links_0064 record009_frame053_links_0128))
theorem record009_frame053_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 53 :=
  of_group record009 53 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0387
    Papers.RationalityTen.SharedFrameCatalogue.group0387_facts record009_frame053_indices record009_frame053_graph record009_frame053_links
def record009_frame054_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xd059db37664cb593b20634c51872b6560ab153aa2538a5547a8950697d2e2594ac94d2824d49491d2224147c8ed1c2354648bd1622944c708de1b83666b8d41a1336654c796b2d0594b115f2b8564ab1532a0534a51472885049f13b2704d4991021fe3f07c8f61e63c0768ea1ce390708de1b63606a8d219e330648b716c2d45a0b31642c4580af15c21041882102200338660ca190318580ae1582a8540a61482885009e1381a8340660c81882604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame054_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame054_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record009) (record009.maps 54) (record009.inverseMaps 54) record009_frame054_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame054_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record009) (record009.maps 54) (record009.inverseMaps 54) record009_frame054_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame054_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record009) (record009.maps 54) (record009.inverseMaps 54) record009_frame054_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame054_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record009) (record009.maps 54)
      (record009.inverseMaps 54) record009_frame054_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame054_links_0000 (interval_append _ 64 128 155 record009_frame054_links_0064 record009_frame054_links_0128))
theorem record009_frame054_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 54 :=
  of_group record009 54 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record009_frame054_indices record009_frame054_graph record009_frame054_links
def record009_frame055_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xdd5b7b6a6c8d75abb50692d0d9e2d85a4b3563ac0574acd562a653e9ed3c2754e49bd362694cc98d3025d4b495d2a25149c92d24245484748e61c73826e8da1ad34c680cc9752e45bcb61692cc58cb015d2b455caa15129c52ca41452844fc9e10c212418819001fa3e87b8f41e23b8758e81ca3886f8dc1b2358698c11802fc5f0bd1782ec5d0b91702304588a1122203586a0d21a03385c0b61682c8580ae1582a8540a61481a8340660c81882604a090118220420800f81e03a0700881001e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record009_frame055_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame055_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record009) (record009.maps 55) (record009.inverseMaps 55) record009_frame055_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame055_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record009) (record009.maps 55) (record009.inverseMaps 55) record009_frame055_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame055_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record009) (record009.maps 55) (record009.inverseMaps 55) record009_frame055_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame055_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record009) (record009.maps 55)
      (record009.inverseMaps 55) record009_frame055_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame055_links_0000 (interval_append _ 64 128 155 record009_frame055_links_0064 record009_frame055_links_0128))
theorem record009_frame055_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 55 :=
  of_group record009 55 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record009_frame055_indices record009_frame055_graph record009_frame055_links
def record009_frame056_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0658.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0658.count (({ width := 9, code := 0x6733598ca6431d8ac3e170579bbdd6e36db5d9ec962afd52a751a7d329347a25067f3e9ecee733699cca5f2c95c522510864220d027fbf5f4ef773b1d4e772389bedc6d365b0d66a3459ccd6531d8cad562a950a5512813a9a4c25d2c944923d188b442150873391c4e06f371b4d86b35164b0572b154a04f271349842209007e3e1e8f0763a1c8e06632188c05e251208c44211007c3c1d0e06c2210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame056_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame056_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record009) (record009.maps 56) (record009.inverseMaps 56) record009_frame056_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame056_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record009) (record009.maps 56) (record009.inverseMaps 56) record009_frame056_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame056_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record009) (record009.maps 56) (record009.inverseMaps 56) record009_frame056_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame056_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record009) (record009.maps 56)
      (record009.inverseMaps 56) record009_frame056_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame056_links_0000 (interval_append _ 64 128 155 record009_frame056_links_0064 record009_frame056_links_0128))
theorem record009_frame056_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 56 :=
  of_group record009 56 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0658
    Papers.RationalityTen.SharedFrameCatalogue.group0658_facts record009_frame056_indices record009_frame056_graph record009_frame056_links
def record009_frame057_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x61b057ebe5eaf176ba5cae162af56ab156aa54aa14ea65067f3c9ccde6b3398cbe5b2c9549e49229047e3b1b8d409fcfa7c3d9e8f2783b9d8e16fb71b2d76ab4da2cf66b3194c76230980bf5eaed74a551a813a9b4ca5d2a9348a411c8b442190883409fcfc72389c0de6e369b0d66a34970b65a2c960a652289409e442190882401f8f87a3c1d8e86a34198c86226128904622108803e1e0e8702210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame057_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame057_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record009) (record009.maps 57) (record009.inverseMaps 57) record009_frame057_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame057_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record009) (record009.maps 57) (record009.inverseMaps 57) record009_frame057_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame057_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record009) (record009.maps 57) (record009.inverseMaps 57) record009_frame057_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame057_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record009) (record009.maps 57)
      (record009.inverseMaps 57) record009_frame057_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame057_links_0000 (interval_append _ 64 128 155 record009_frame057_links_0064 record009_frame057_links_0128))
theorem record009_frame057_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 57 :=
  of_group record009 57 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record009_frame057_indices record009_frame057_graph record009_frame057_links
def record009_frame058_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0856.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0856.count (({ width := 9, code := 0x40a00fd7dbe5eef579bc5deea74395c6e16fb75b6d96bb51a6d2683399acc6532590c76331586c1602fd7abc5dac15cab54a9d4aa350a7d3a9a4ca612c9449a49208f47235188b44a1d0c8541a0902783b9d8e872389c0dc6d361acd46933994c86330980be572b154a85329144a04f271188a44219087e3e1e8f076361a8d06632188c05e2e168b05228138984a200f8783a1c0d86832180b8582210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame058_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame058_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record009) (record009.maps 58) (record009.inverseMaps 58) record009_frame058_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame058_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record009) (record009.maps 58) (record009.inverseMaps 58) record009_frame058_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame058_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record009) (record009.maps 58) (record009.inverseMaps 58) record009_frame058_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame058_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0856.localPairCheck (smallEmbedding record009) (record009.maps 58)
      (record009.inverseMaps 58) record009_frame058_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame058_links_0000 (interval_append _ 64 128 155 record009_frame058_links_0064 record009_frame058_links_0128))
theorem record009_frame058_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 58 :=
  of_group record009 58 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0856
    Papers.RationalityTen.SharedFrameCatalogue.group0856_facts record009_frame058_indices record009_frame058_graph record009_frame058_links
def record009_frame059_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1038.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1038.count (({ width := 9, code := 0x50e833f9ecee73379acce61269248a411e8e46a311689c2e15088341205017fbf5f8fa7cbddeaf378bc1dcec75b65aed569b459ecd65b258cbe5eaed72b75aad164b057ab558aa5429948a350a7d3c8e46a2d128742a1104803f9f4f87a3c1d8e873389bcdc653218cc4613017cbc5d2e148a25027938964a249208e3e1e8f0763a1c8e06e361a8d06230178b85a241188842200f8783a1c0d8682210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame059_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame059_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record009) (record009.maps 59) (record009.inverseMaps 59) record009_frame059_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame059_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record009) (record009.maps 59) (record009.inverseMaps 59) record009_frame059_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame059_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record009) (record009.maps 59) (record009.inverseMaps 59) record009_frame059_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame059_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1038.localPairCheck (smallEmbedding record009) (record009.maps 59)
      (record009.inverseMaps 59) record009_frame059_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame059_links_0000 (interval_append _ 64 128 155 record009_frame059_links_0064 record009_frame059_links_0128))
theorem record009_frame059_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 59 :=
  of_group record009 59 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1038
    Papers.RationalityTen.SharedFrameCatalogue.group1038_facts record009_frame059_indices record009_frame059_graph record009_frame059_links
def record009_frame060_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0706.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0706.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame060_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0706.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame060_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0706.localPairCheck (smallEmbedding record009) (record009.maps 60) (record009.inverseMaps 60) record009_frame060_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame060_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0706.localPairCheck (smallEmbedding record009) (record009.maps 60) (record009.inverseMaps 60) record009_frame060_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame060_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0706.localPairCheck (smallEmbedding record009) (record009.maps 60) (record009.inverseMaps 60) record009_frame060_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame060_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0706.localPairCheck (smallEmbedding record009) (record009.maps 60)
      (record009.inverseMaps 60) record009_frame060_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame060_links_0000 (interval_append _ 64 128 155 record009_frame060_links_0064 record009_frame060_links_0128))
theorem record009_frame060_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 60 :=
  of_group record009 60 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0706
    Papers.RationalityTen.SharedFrameCatalogue.group0706_facts record009_frame060_indices record009_frame060_graph record009_frame060_links
def record009_frame061_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0727.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0727.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame061_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0727.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame061_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0727.localPairCheck (smallEmbedding record009) (record009.maps 61) (record009.inverseMaps 61) record009_frame061_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame061_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0727.localPairCheck (smallEmbedding record009) (record009.maps 61) (record009.inverseMaps 61) record009_frame061_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame061_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0727.localPairCheck (smallEmbedding record009) (record009.maps 61) (record009.inverseMaps 61) record009_frame061_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame061_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0727.localPairCheck (smallEmbedding record009) (record009.maps 61)
      (record009.inverseMaps 61) record009_frame061_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame061_links_0000 (interval_append _ 64 128 155 record009_frame061_links_0064 record009_frame061_links_0128))
theorem record009_frame061_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 61 :=
  of_group record009 61 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0727
    Papers.RationalityTen.SharedFrameCatalogue.group0727_facts record009_frame061_indices record009_frame061_graph record009_frame061_links
def record009_frame062_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0682.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0682.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame062_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0682.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame062_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0682.localPairCheck (smallEmbedding record009) (record009.maps 62) (record009.inverseMaps 62) record009_frame062_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame062_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0682.localPairCheck (smallEmbedding record009) (record009.maps 62) (record009.inverseMaps 62) record009_frame062_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame062_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0682.localPairCheck (smallEmbedding record009) (record009.maps 62) (record009.inverseMaps 62) record009_frame062_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame062_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0682.localPairCheck (smallEmbedding record009) (record009.maps 62)
      (record009.inverseMaps 62) record009_frame062_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame062_links_0000 (interval_append _ 64 128 155 record009_frame062_links_0064 record009_frame062_links_0128))
theorem record009_frame062_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 62 :=
  of_group record009 62 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0682
    Papers.RationalityTen.SharedFrameCatalogue.group0682_facts record009_frame062_indices record009_frame062_graph record009_frame062_links
def record009_frame063_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0949.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0949.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame063_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0949.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame063_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0949.localPairCheck (smallEmbedding record009) (record009.maps 63) (record009.inverseMaps 63) record009_frame063_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame063_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0949.localPairCheck (smallEmbedding record009) (record009.maps 63) (record009.inverseMaps 63) record009_frame063_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame063_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0949.localPairCheck (smallEmbedding record009) (record009.maps 63) (record009.inverseMaps 63) record009_frame063_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame063_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0949.localPairCheck (smallEmbedding record009) (record009.maps 63)
      (record009.inverseMaps 63) record009_frame063_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame063_links_0000 (interval_append _ 64 128 155 record009_frame063_links_0064 record009_frame063_links_0128))
theorem record009_frame063_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 63 :=
  of_group record009 63 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0949
    Papers.RationalityTen.SharedFrameCatalogue.group0949_facts record009_frame063_indices record009_frame063_graph record009_frame063_links
def record009_frame064_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0513.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0513.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame064_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0513.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame064_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0513.localPairCheck (smallEmbedding record009) (record009.maps 64) (record009.inverseMaps 64) record009_frame064_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame064_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0513.localPairCheck (smallEmbedding record009) (record009.maps 64) (record009.inverseMaps 64) record009_frame064_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame064_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0513.localPairCheck (smallEmbedding record009) (record009.maps 64) (record009.inverseMaps 64) record009_frame064_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame064_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0513.localPairCheck (smallEmbedding record009) (record009.maps 64)
      (record009.inverseMaps 64) record009_frame064_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame064_links_0000 (interval_append _ 64 128 155 record009_frame064_links_0064 record009_frame064_links_0128))
theorem record009_frame064_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 64 :=
  of_group record009 64 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0513
    Papers.RationalityTen.SharedFrameCatalogue.group0513_facts record009_frame064_indices record009_frame064_graph record009_frame064_links
def record009_frame065_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1107.count (({ width := 9, code := 0x4be5d2d964aa51269248a41188bc5a2b1388c3e1b0b84c0a03007fbf5f6f97bbd5e6f1783bddced763add4e974375b8db6d361acd4693419cc76331588c2602f978ba5c2d96ab459ac962b057ab95aa351285409e4e26930964a249229047a391a8c45a29128441a0902803f9f8fa7c3d9a8d26833998b4592c15cac4b251249047231148843211046a34198c86226128904622108803e1e0e8702210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame065_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame065_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record009) (record009.maps 65) (record009.inverseMaps 65) record009_frame065_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame065_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record009) (record009.maps 65) (record009.inverseMaps 65) record009_frame065_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame065_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record009) (record009.maps 65) (record009.inverseMaps 65) record009_frame065_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame065_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record009) (record009.maps 65)
      (record009.inverseMaps 65) record009_frame065_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame065_links_0000 (interval_append _ 64 128 155 record009_frame065_links_0064 record009_frame065_links_0128))
theorem record009_frame065_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 65 :=
  of_group record009 65 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1107
    Papers.RationalityTen.SharedFrameCatalogue.group1107_facts record009_frame065_indices record009_frame065_graph record009_frame065_links
def record009_frame066_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1088.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1088.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame066_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1088.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame066_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1088.localPairCheck (smallEmbedding record009) (record009.maps 66) (record009.inverseMaps 66) record009_frame066_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame066_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1088.localPairCheck (smallEmbedding record009) (record009.maps 66) (record009.inverseMaps 66) record009_frame066_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame066_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1088.localPairCheck (smallEmbedding record009) (record009.maps 66) (record009.inverseMaps 66) record009_frame066_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame066_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1088.localPairCheck (smallEmbedding record009) (record009.maps 66)
      (record009.inverseMaps 66) record009_frame066_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame066_links_0000 (interval_append _ 64 128 155 record009_frame066_links_0064 record009_frame066_links_0128))
theorem record009_frame066_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 66 :=
  of_group record009 66 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1088
    Papers.RationalityTen.SharedFrameCatalogue.group1088_facts record009_frame066_indices record009_frame066_graph record009_frame066_links
def record009_frame067_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1085.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1085.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame067_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1085.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame067_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1085.localPairCheck (smallEmbedding record009) (record009.maps 67) (record009.inverseMaps 67) record009_frame067_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame067_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1085.localPairCheck (smallEmbedding record009) (record009.maps 67) (record009.inverseMaps 67) record009_frame067_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame067_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1085.localPairCheck (smallEmbedding record009) (record009.maps 67) (record009.inverseMaps 67) record009_frame067_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame067_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1085.localPairCheck (smallEmbedding record009) (record009.maps 67)
      (record009.inverseMaps 67) record009_frame067_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame067_links_0000 (interval_append _ 64 128 155 record009_frame067_links_0064 record009_frame067_links_0128))
theorem record009_frame067_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 67 :=
  of_group record009 67 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1085
    Papers.RationalityTen.SharedFrameCatalogue.group1085_facts record009_frame067_indices record009_frame067_graph record009_frame067_links
def record009_frame068_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0261.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0261.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame068_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0261.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame068_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0261.localPairCheck (smallEmbedding record009) (record009.maps 68) (record009.inverseMaps 68) record009_frame068_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame068_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0261.localPairCheck (smallEmbedding record009) (record009.maps 68) (record009.inverseMaps 68) record009_frame068_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame068_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0261.localPairCheck (smallEmbedding record009) (record009.maps 68) (record009.inverseMaps 68) record009_frame068_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame068_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0261.localPairCheck (smallEmbedding record009) (record009.maps 68)
      (record009.inverseMaps 68) record009_frame068_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame068_links_0000 (interval_append _ 64 128 155 record009_frame068_links_0064 record009_frame068_links_0128))
theorem record009_frame068_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 68 :=
  of_group record009 68 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0261
    Papers.RationalityTen.SharedFrameCatalogue.group0261_facts record009_frame068_indices record009_frame068_graph record009_frame068_links
def record009_frame069_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0649.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0649.count (({ width := 8, code := 0xfbfaf9f8f7f6f5f3f1f0eeedecebeae9e8e6e4e3e1e0dfdedddbd9d7d5d3d1cfcdcbc9c7c6c4c1bfb8b7b6b5b4b2b0aeacaaa8a7a6a5a4a3a2a09e9d9b9997959391908e8b898281807f7e7d7c7a78777573716f6d6b6a6865635c5a58565452514f4c4a3c3b3a39383534333231302f2e2d2c2b2a2928272625242322211e1d1c1b1a19181716151411100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame069_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0649.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame069_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record009) (record009.maps 69) (record009.inverseMaps 69) record009_frame069_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame069_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record009) (record009.maps 69) (record009.inverseMaps 69) record009_frame069_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame069_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record009) (record009.maps 69) (record009.inverseMaps 69) record009_frame069_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame069_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record009) (record009.maps 69)
      (record009.inverseMaps 69) record009_frame069_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame069_links_0000 (interval_append _ 64 128 155 record009_frame069_links_0064 record009_frame069_links_0128))
theorem record009_frame069_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 69 :=
  of_group record009 69 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0649
    Papers.RationalityTen.SharedFrameCatalogue.group0649_facts record009_frame069_indices record009_frame069_graph record009_frame069_links
def record009_frame070_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1084.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1084.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame070_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1084.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame070_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1084.localPairCheck (smallEmbedding record009) (record009.maps 70) (record009.inverseMaps 70) record009_frame070_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame070_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1084.localPairCheck (smallEmbedding record009) (record009.maps 70) (record009.inverseMaps 70) record009_frame070_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame070_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1084.localPairCheck (smallEmbedding record009) (record009.maps 70) (record009.inverseMaps 70) record009_frame070_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame070_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1084.localPairCheck (smallEmbedding record009) (record009.maps 70)
      (record009.inverseMaps 70) record009_frame070_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame070_links_0000 (interval_append _ 64 128 155 record009_frame070_links_0064 record009_frame070_links_0128))
theorem record009_frame070_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 70 :=
  of_group record009 70 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1084
    Papers.RationalityTen.SharedFrameCatalogue.group1084_facts record009_frame070_indices record009_frame070_graph record009_frame070_links
def record009_frame071_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0502.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0502.count (({ width := 8, code := 0x9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame071_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0502.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame071_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0502.localPairCheck (smallEmbedding record009) (record009.maps 71) (record009.inverseMaps 71) record009_frame071_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame071_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0502.localPairCheck (smallEmbedding record009) (record009.maps 71) (record009.inverseMaps 71) record009_frame071_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame071_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0502.localPairCheck (smallEmbedding record009) (record009.maps 71) (record009.inverseMaps 71) record009_frame071_indices (Fin.ofNat record009.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record009_frame071_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0502.localPairCheck (smallEmbedding record009) (record009.maps 71)
      (record009.inverseMaps 71) record009_frame071_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record009_frame071_links_0000 (interval_append _ 64 128 155 record009_frame071_links_0064 record009_frame071_links_0128))
theorem record009_frame071_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 71 :=
  of_group record009 71 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0502
    Papers.RationalityTen.SharedFrameCatalogue.group0502_facts record009_frame071_indices record009_frame071_graph record009_frame071_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (Fin.cases (record009_frame008_supported hcells) (Fin.cases (record009_frame009_supported hcells) (Fin.cases (record009_frame010_supported hcells) (Fin.cases (record009_frame011_supported hcells) (Fin.cases (record009_frame012_supported hcells) (Fin.cases (record009_frame013_supported hcells) (Fin.cases (record009_frame014_supported hcells) (Fin.cases (record009_frame015_supported hcells) (Fin.cases (record009_frame016_supported hcells) (Fin.cases (record009_frame017_supported hcells) (Fin.cases (record009_frame018_supported hcells) (Fin.cases (record009_frame019_supported hcells) (Fin.cases (record009_frame020_supported hcells) (Fin.cases (record009_frame021_supported hcells) (Fin.cases (record009_frame022_supported hcells) (Fin.cases (record009_frame023_supported hcells) (Fin.cases (record009_frame024_supported hcells) (Fin.cases (record009_frame025_supported hcells) (Fin.cases (record009_frame026_supported hcells) (Fin.cases (record009_frame027_supported hcells) (Fin.cases (record009_frame028_supported hcells) (Fin.cases (record009_frame029_supported hcells) (Fin.cases (record009_frame030_supported hcells) (Fin.cases (record009_frame031_supported hcells) (Fin.cases (record009_frame032_supported hcells) (Fin.cases (record009_frame033_supported hcells) (Fin.cases (record009_frame034_supported hcells) (Fin.cases (record009_frame035_supported hcells) (Fin.cases (record009_frame036_supported hcells) (Fin.cases (record009_frame037_supported hcells) (Fin.cases (record009_frame038_supported hcells) (Fin.cases (record009_frame039_supported hcells) (Fin.cases (record009_frame040_supported hcells) (Fin.cases (record009_frame041_supported hcells) (Fin.cases (record009_frame042_supported hcells) (Fin.cases (record009_frame043_supported hcells) (Fin.cases (record009_frame044_supported hcells) (Fin.cases (record009_frame045_supported hcells) (Fin.cases (record009_frame046_supported hcells) (Fin.cases (record009_frame047_supported hcells) (Fin.cases (record009_frame048_supported hcells) (Fin.cases (record009_frame049_supported hcells) (Fin.cases (record009_frame050_supported hcells) (Fin.cases (record009_frame051_supported hcells) (Fin.cases (record009_frame052_supported hcells) (Fin.cases (record009_frame053_supported hcells) (Fin.cases (record009_frame054_supported hcells) (Fin.cases (record009_frame055_supported hcells) (Fin.cases (record009_frame056_supported hcells) (Fin.cases (record009_frame057_supported hcells) (Fin.cases (record009_frame058_supported hcells) (Fin.cases (record009_frame059_supported hcells) (Fin.cases (record009_frame060_supported hcells) (Fin.cases (record009_frame061_supported hcells) (Fin.cases (record009_frame062_supported hcells) (Fin.cases (record009_frame063_supported hcells) (Fin.cases (record009_frame064_supported hcells) (Fin.cases (record009_frame065_supported hcells) (Fin.cases (record009_frame066_supported hcells) (Fin.cases (record009_frame067_supported hcells) (Fin.cases (record009_frame068_supported hcells) (Fin.cases (record009_frame069_supported hcells) (Fin.cases (record009_frame070_supported hcells) (Fin.cases (record009_frame071_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record009_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013
