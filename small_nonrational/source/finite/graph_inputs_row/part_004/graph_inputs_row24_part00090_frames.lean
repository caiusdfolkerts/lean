module
prelude
public import GraphInputsRow24Part00090Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x85580f7c97b472e71b6f16e96cb69c6906426226055e35c55b058556055953f5284e24d049b4774614334173c33ac3a338937b34633b3263092ef2de2a92812632492302272212172041dd1d21c41af19618014f1471321181050f50ea0c10b907c07707206e06b05905405304904103502c02502401f01e01200f00d00a009008004003001000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x19aac6c60cab1d4cea414e226392be929484a40d0e8841418a004fe27363589a04ca062030117f4b1856529b94409e44ca24111cc8ba45122210b88443b01be0d4063830314609e44b424d11f08804262040ec068c3241800bb05b02c014f0a284ec25e09e04601e80d205a02b81580aa054021810806202f015009804401f00f007403801700a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x1c1b736b4cb18bb045d8b896cace588b014ba885049c13524f45e8950e20c4027ecee1d138a6e0d49983085fcbb9722d6590b014b27a4d49211c1e83c4730e31bc34c680cc1822cc570ab15029c5209e1342604a0730d21942d84e096128248480861081882f0540981101f03c0740e0170280400680a0120200380400600800800 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x2bbd5da7737e61cad8f117224432835049efbc877ce91cdb6d66ac7d88afd5daba1612b4540a3d39a604808e916224434825009da37e6c8d09942c2568a49422704a08f9192103d8788ec1ca3846d8d219a320618890f81d0338580aa150298520861081882f0540981101f03c0740e0170280400680a0120200380400600800800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x4b391d1fa3745e8a111e16c1f816fd9f13d773ee31c2b6b6c4d198eb10606bd1732de588ad152a955049e12623f4748990fa083f87a0f09d538065cc29802f25bcb395e2a4524a013724e458881092023e8788e51b43446206e0d21a02c84c0921202384607e0f81782203e0780e81c03405c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xb8357b2b1d52ca67524290538298e4ae24a521490343a21050628013f89cd8d626813281880c045fd2c81594a7651027b93c890445d22890b88443be1d60df06bc34c18e0b34518279133896849a23e11688804262040ed068c3241820bb05b02c01510a284ec25e08c03d81e80d205a02b81580aa054021810806202200f807803a01c00d005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x4087dcf91efbd4790f0dd4397716df5b6b6765cc59862f55dcb3155a9f532a3d4127d4d897d2ba4d4828f5091ff3ee790ef9b9366688cd99430c58ca41402744c497124238454869091ee3906f8d91a6340650c317c2e45a0740d61a82f85009a1302584a0821001882203e0780e81c03405c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xc3a5b5ace15feac654d2a193fe9cc4c9a56925c91a465a2d915e89a4499f60e306e935b1a0ccb86492e19650ac252e28393d094a49024491d88e04031f40e986fe3681950aa04f226b12d092c47822d10e08344001f20e286583101770b40564294139095047421e08c03d81e80d205a02b81580aa054021810806202200f807803a01c00d005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame004_links_0000 record006_frame004_links_0064)
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x3e4786ed5d439470adf9b0b5468ecd992b1b5f0b9d712d1598a9540a734ce94d22a3f43c849021f43ca770dc9a9348650c81752e058caf95627e48c8a91321e428831011f63d0788e71b2340658c81842f45d0b315a2985106c0ce1982c84e096128248480760e81682203e0780e81c03405c0a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame005_links_0000 record006_frame005_links_0064)
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7707166f26d16b96a469d65b6436225fe5e65df5ad59859157c5755104b149046f4524384313ec3cf3a938836f36833732231c3073012cc2b928e2742612361f81d11c61bb1b21ac1a319718f18717e16213b13012411c11410b1020f90f30ea08c07b07a06905a05705605505404304203102201f01e01d01c01a01701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame006_links_0000 record006_frame006_links_0064)
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0122.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0122.count (({ width := 7, code := 0x6edbb35ead3a33e6cb931e2c382fdebb72ddab362bd6ab529d2a3427ce9b325c68b0a0c07af1cb86ed9ab466c98b05eb15aa52a13a64a911a24280f9e3a70d9a3260b962a50992223868c16284880e182840608080 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0122.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0122.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0122.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0122.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame007_links_0000 record006_frame007_links_0064)
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0122
    Papers.RationalityTen.SharedFrameCatalogue.group0122_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
def record006_frame008_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0240.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0240.count (({ width := 8, code := 0xcecbc8c7c4c3c2bfbcbbb8b7b6b5b4b3b2b1aaa7a4a3a09f9e9b989794939291908f8e8d7f7c7674716b67615f5c5a58565452504e4b4543403e3c3a383634322a2726242221201f1e1b1a181615141312110e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0240.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0240.localPairCheck (smallEmbedding record006) (record006.maps 8)
      (record006.inverseMaps 8) record006_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame008_links_0000 record006_frame008_links_0064)
theorem record006_frame008_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 8 :=
  of_group record006 8 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0240
    Papers.RationalityTen.SharedFrameCatalogue.group0240_facts record006_frame008_indices record006_frame008_graph record006_frame008_links
def record006_frame009_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0119.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0119.count (({ width := 8, code := 0x8b88858481807f7c79787574737271706f6e686562615e5d5c5956555251504f4e4d4c4b46454241403d3c393837363534333231302f2c2b2a292827262524232221201f1e1d1c1b1a1918171615141312110e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0119.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0119.localPairCheck (smallEmbedding record006) (record006.maps 9)
      (record006.inverseMaps 9) record006_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame009_links_0000 record006_frame009_links_0064)
theorem record006_frame009_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 9 :=
  of_group record006 9 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0119
    Papers.RationalityTen.SharedFrameCatalogue.group0119_facts record006_frame009_indices record006_frame009_graph record006_frame009_links
def record006_frame010_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc075962bc5566a7652528d534896d49a23f11a28be4181fecfd27b73d39b4cbf05bd2bf9508a2c50123810e48003c81ce8e285f82c715a8a0c4e6239118086c41e2060f887043581a60cf065c32218a0c105ec2ea16e0ac050c27a13509704a0242119089043020a08c03d81e80d205a02b81580aa054021810806202200f807803a01c00d005c02a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record006_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 10)
      (record006.inverseMaps 10) record006_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame010_links_0000 record006_frame010_links_0064)
theorem record006_frame010_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 10 :=
  of_group record006 10 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame010_indices record006_frame010_graph record006_frame010_links
def record006_frame011_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x7c47507307106ef6d16c565f63b6185f35d05c256e55554c53452c4e146544141e3f93d63c83623423223012e32d728b2722692512492202182051fa1f11dd1af19819018718017917116816115b15313d12611e11510e1070ff0f60ef0e90e108c07b07a06905a05705605505404304203102201f01e01d01c01a01701501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record006_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 11)
      (record006.inverseMaps 11) record006_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame011_links_0000 record006_frame011_links_0064)
theorem record006_frame011_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 11 :=
  of_group record006 11 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record006_frame011_indices record006_frame011_graph record006_frame011_links
def record006_frame012_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x1ec781d7749ca721c56f5b66c9ab699a465d936458f631825c9695915d561565414850d3c4dd344b129495224850f424fe3e8f63a4d4324c730cbe2ecb62c8ad2a8a626c8e230882107e1e4761cc6e1ac4810c420f0360cc320c4300ac2a0881c06c1a0641805813044100380d02c09020070180400c0200400 } : Fields).get c.val)
theorem record006_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record006) (record006.maps 12) (record006.inverseMaps 12) record006_frame012_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record006) (record006.maps 12) (record006.inverseMaps 12) record006_frame012_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record006) (record006.maps 12)
      (record006.inverseMaps 12) record006_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame012_links_0000 record006_frame012_links_0064)
theorem record006_frame012_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 12 :=
  of_group record006 12 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record006_frame012_indices record006_frame012_graph record006_frame012_links
def record006_frame013_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0239.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0239.count (({ width := 8, code := 0x9c9996959291908d8a89868584838281807f787572716e6d6c6966656261605f5e5d5c5b52514e4d4c49484544434241403f3e3d3c3b3837363534333231302f2c29282624232221201d1c1a1817161514120f0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0239.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record006) (record006.maps 13) (record006.inverseMaps 13) record006_frame013_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record006) (record006.maps 13) (record006.inverseMaps 13) record006_frame013_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record006) (record006.maps 13)
      (record006.inverseMaps 13) record006_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame013_links_0000 record006_frame013_links_0064)
theorem record006_frame013_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 13 :=
  of_group record006 13 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0239
    Papers.RationalityTen.SharedFrameCatalogue.group0239_facts record006_frame013_indices record006_frame013_graph record006_frame013_links
def record006_frame014_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0118.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0118.count (({ width := 7, code := 0x60bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record006_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0118.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0118.localPairCheck (smallEmbedding record006) (record006.maps 14) (record006.inverseMaps 14) record006_frame014_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0118.localPairCheck (smallEmbedding record006) (record006.maps 14) (record006.inverseMaps 14) record006_frame014_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0118.localPairCheck (smallEmbedding record006) (record006.maps 14)
      (record006.inverseMaps 14) record006_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame014_links_0000 record006_frame014_links_0064)
theorem record006_frame014_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 14 :=
  of_group record006 14 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0118
    Papers.RationalityTen.SharedFrameCatalogue.group0118_facts record006_frame014_indices record006_frame014_graph record006_frame014_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (Fin.cases (record006_frame008_supported hcells) (Fin.cases (record006_frame009_supported hcells) (Fin.cases (record006_frame010_supported hcells) (Fin.cases (record006_frame011_supported hcells) (Fin.cases (record006_frame012_supported hcells) (Fin.cases (record006_frame013_supported hcells) (Fin.cases (record006_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x853041fbbc572ce09b635f6a4ce596b1a60ec1177ae754ea2934a564949151121240a7f0ef9d238c6e0d89ad344664c997c2cc560a493d26c4ac8f1182003c8760e61b232c638c41822fc5e0b816428c4d8790dc1882e8530a413c2684c07a0d01682b0500901082003a06c0d0170280380680b0140200380400600800800 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0xf29dc3ad734e49c4b826cad319cb26636be1762d1582ad555a98518a093ea6449e89909a0e3da768e59c33706a8cf9893065fcb115226248c9011821a4007d8f91c4364640bf1742cc5289912a24c478780ee1c8320620ba16c2a84e09a130240470680bc1682b05008c1102003a0700780e01a0280400700600800800 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0249.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0249.count (({ width := 9, code := 0x49a311487c32150880bd9deea73379b6d467b3192c660afd7cb658295429e4ba41168742204fe783b9d8e26e34998c8612f170b65a299409a4b2512086401f8f87a33190bc582b1409c4a22108803e1e0d05c2c150a044200f070341208038180a04018080200 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0249
    Papers.RationalityTen.SharedFrameCatalogue.group0249_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0123.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0123.count (({ width := 8, code := 0xb7b0aeaaa9a8a7a59f9a9795928f8b89878683807f7e7a766f6d6b6964615f5d5c5a56555452514d4c4b4948464544403d3c3a3938353231302f252423201f1e1d1c1b1a19181714131211100f0e0d0c0b09080706050403020100 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0123.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0123.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0123.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0123.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0123
    Papers.RationalityTen.SharedFrameCatalogue.group0123_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8758257ea7c47b57b17116f469569361d6005d75d55c05b159759357b5775705064fc4b548d42e4223ad38536535932431b3093002fc2b529125d23921320d1fb1ce1bb1b31a71a018917f17616513811610c1020fa0ee0e70e00ce0ca0c60c20b909608608007b07906f05c05805704304003b03602c02302001e01501100d00b008005001000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x9a659936469023e8921e81a057b5e776dda755cf719c36edb86d19f66d92631765c5605695052d3b4e1304b52a4590b400f53a0e5384d432cc7308bf2ccae2a4a425c862047a1d8711b86c18c6117c5c1605012c4a1244710c3c0e0370bc2c0ac28094210781c054110340b0200500400 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0519.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0519.count (({ width := 10, code := 0x852077f1f57c1ee75dd26fdbe6b9a86759c65d8f61d845f97b5dd6357955541404ed314b926485114390640d003bce837cd7320c4300b52c0ad2a4a6270972488e2207c1e0751cc6e1ac691785b164561484c11c4610c420fc380d0330ac28094210781b064180440f02c090180400400 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record014_frame003_links_0000 record014_frame003_links_0064)
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0519
    Papers.RationalityTen.SharedFrameCatalogue.group0519_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8758257ea7c47b57b176671b6f469a6936276005dc5d55b159a59357e5775704fc4ee4ad48d4824464294223c33a538537a36035934833732131b3063002fc2b729125f23921420d1fa1ce1bb1b31a91a018817f17616413811510c1020fa0f00e70e00cf0ca0c60c20b909607b05804e04804304104003b03703602c02402302001f01e01501100d00b008005001000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0xf0f83bfdeeef73a3c7e06b75598c8e270d7ebd5e2e771b7586bf56a7d32833c9dcb24d1f8e4622f1488c3a190983c19eaec7035d9ccc642ed66af54a95329549235007036198c45c2c15ca451279349449218d85a2c158a45027130944622108783a1c0a8441a0b040140200 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0520.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0520.count (({ width := 9, code := 0xe6f2789c1dfef767a9d26632b88c1deef171b65aac962af53295439fcf67130974923f1c8cc4e230e8441202fc7cbd9cade6ab3584bf5dac558a952a8934974a2450e7b3c1d4e86e359a4c25f2e968ac55278f46a34190c05e2d158a84c22108783a1c0a8441a0b040140200 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0520
    Papers.RationalityTen.SharedFrameCatalogue.group0520_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record015_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090
