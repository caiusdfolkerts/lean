module
prelude
public import GraphInputsRow30Part00059Data
public import RawFrameSupport
public import SharedFrameGroups006Checked
public import SharedFrameGroups012Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups058Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x38fd962ca464b3235912c8163d2b39580ab9559aaa5548a9d4a9a4ed25491b4852281110877434215d09a84541ea0d905e78d37199f0cea66f3341984cb46513251914c7e56c2a894d4a2a50a27e137c9884a824411f48de465230916c8ac4511a78cc063e30b1770b7455c28f13f09a849a23c11908a844621c10a868831617b0b5055c28a13b08403f81a409e04a01e80e005c02d81680ae05602a810c08403901c00a804c024011808804201f00f0074028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x17dec6582ae5582afd57aa138a6a4cb9872ce584a98ad13222c42877052054037fefe1f8be87baf5de8baf70ad85aeb5769ad0d9db2963cc7189ac857cab54da9751aa053926249c92120a3545e8890ca113926ecd91a7338648bf9702ce570a694627a4c49391e22c3e0788ec1ce3846d8d51802ec530891041c0348560aa1502885009e10c210390700a8130240460881081f03c0740a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x349583ac035f72f697a4bb45cf29fd4d0a6052c28c9448a11496244d1fc8ea46a21c50b284641a207d01c7f63ee1f18f5e75b3789a9cd3268833e19accc264e31e18c8c425972bd9594a8453629414209d44d22571288928482239917c8a04401c60db06c434f1948c5c5c62c215c0a9450226f12e891c46822210706e43501970c305d82c6150087040019209e04a01e80e005c02d81680ae05602a810c08403901c00a804c024011808804201f00f0074028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x70267e67767266a66665f65b5cb5c35c05bb5b25ad5a852951a50f5095004d14c24b74b24a94a349b49348f48b4463f73c53c03bb3b73b23af3a73a139d3993313213183002fd2f62e22d82c92b12ad2a72a029c29629329021e20d2091fb1e81e01c41b91b21a419018a18317b17417016c13712811f11610b0fe0f60d40cc0ae09208c07606e05a05905805505405304204103903802a02602402302202101f01e01d01401000f00e00d00b00a009008004003002001000 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x117a08c06802fd9fabef7d0e75cbb90714e05beb77680ce59ab3265ac4986307608bf97d2f55dab9971ac15229c1352634ba95d292494889091ea073f87dcf39e53be74ce49c13626b4d39a133c65cc918f2a4528a293d2624ac8f11a228430800fa1ee3c4750e51c631c620c117e2f05c0b314a28c4a8790ea19c310540a61482784e09a0f41e0350680a0120220420800f81d03806c0a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a1a2acfb6052ac5512a5f525a8e923c8fa473a35917e83040e2030ff67e93eb1f1cf2a6d62be9554a565172830fa878c3b31d10e2c5f82e816c0b1c56a2a2149898447220f10408043f41f30f6078c3b81c20da069832e1910c505ec2ce1520a204f426a12809084641fc0f6078023811a07103681ac0d406102e81700b605702b01540a803901a80cc064029012809004601f00f007403801500a004402000f0070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65f65a6566335c95bd5ab59d59552751850c5044f64bb4b44ae4a94a249b4954834623f23e63d43c83bf34c33c33132931d2e02d82d22cd2c62c02bb2ae28924924023322721d2132061f91d51c41b119819118617215513e12c1211141010f60ec0c50bc0b808408306e06a06806705f05b05a05905505405305203803403203102902502402301f01e01d01c01501401101000f00e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2fb57c6bca5a92a214e2a5f525a8e52b2936496246d1fe87142e212106881f4031fccf6275e34b19e4cc06513219628adc5652ad150c9a44c1258128892848123811088023ad1cd8e306f636c1b10d406762f41698ae052628113789204201e00e186e43541860bb0594242110080823811a07103681ac0d406102e81700b605702b01540a803901a80cc064029012809004601f00f007403801500a004402000f0070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6c66b666b5e85d85cd5c15b953d52a52551e50e4c94bd4b14a749a48c4844644313ad39f39338737f3012f22eb2e42d428f28327726a25f25224a22a2091e11d91d01c81bf1b91b41ad19017f17016515f15714913212211611010c1010f90f20da0d40d008a08906f06b06906805f05b05a05905505405305203903503303202902502402301f01e01d01c01501401101000f00e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x101a013ff7cae99cbb9070ce05a033465aca18e2f85e4bad73ae25b4b5163aa64ca95d27a464847f8f91ec3d0774dc9b335a6a4d219d32e62cba95f2b0544a51412744cc9712423644c851062023d0710d61a232c640bd1742cc4d0951221b8368600ba16c2d0540a21402784b094124240340620bc1702804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0xe35c5b846d0ce99932b64ac8972adc5aeb51652a4540a694aa8f516a193d26a4648a11021a42c77ced9d73a8728d31a1338658c918c3105f0b214928a4fc9d9362624b49391a22041c7e8f91ea3a8700d1194318608b81662b44f89b12e1d0398620be1742e0540a013c2704a092120238350620bc1702804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc7c5f82fa57a6bba5d22b8d4bea4c51b288541c9d549624612008ea46a23151668a144821f90e485a42220dd04480c3fb9f64f867ac3789980ca46403179878bd45652ab9510a6c52828e142c9f84ed26f134c97e4ac252925c90e47422e113487a4011b10d4467832918b8c185e82e31698b08570281137896c4921fd0f707803a21c30dc86182ec1660a8843c1fe0f2072835818e07103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame001_links_0000 (interval_append _ 64 128 129 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x4ed9ab34a674ca98d2522d4518911061d4347dcf91ecbcf788efddcbb275eea1d0399724e39c3b7e6eada1afb5b644bbd73adf5b2b4564a8e5089e9392694ca98d2da584aa935242434828f11b22f4468710ca083766d8d81ab34a67ccc19231c618c01672bc54ca512d2504848e9172203e8788e61b62c05389d12823c448610c016c2d0590a814c2704d0980dc1b0310600bc1502904808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame002_links_0000 (interval_append _ 64 128 129 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd5768534119facf56772df1560a9c54429e14cca104a224c123890c47d23bd1d08e146d234d1988c345e22dd1608a9451226512488b39399c8cbc64b31c98a0ba451d28493d89c84d326413049744b3256929893a496248922890647d23a91bc8d240318c8c0c5de2da1638ae455229914509e84d623c116887441c1d60e306d834e1970c4056429413a09583dc1e00e9071036c1a807103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame003_links_0000 (interval_append _ 64 128 129 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe30698b471a0acea669acfd4bea4c51ba8914209b6473a34d1808ad44d222d0f286742aa11506681a4041ff8fd87dc3e59ec8f4479030594aca3050327813709043b31cf8e306f23661ab8d146663211888bfc5cc2d41650ae055029713f09b84b82390f607903ba1d70e807243841bb0da06b434c1910c5060c2f81600ac854829614409e84a024211a08983d41dc0e707003641a607103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame004_links_0000 (interval_append _ 64 128 129 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x71a6d16ca6bc6ad6a16255cd5c25b65ac59f57d52551b50f5054f84f14ea4e24db4d14ca4bb4ad4aa49d49248847646a45f3eb39338837c36f3653432eb2e12d52c82bf2b72af2a529f29729028127326d26225824e23922f2252091b91b51ae1a81a019819018817f17717015f15714f14a12d12812211c1161101010f90f30ee0d30ce0c70bf0b80b206f06e06906806706005f05a05905803903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame005_links_0000 (interval_append _ 64 128 129 record002_frame005_links_0064 record002_frame005_links_0128))
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0562.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0562.count (({ width := 11, code := 0x4107ccf7dedbd67a0ed9c73896fede5b7b6666ecc194324636c5989b0b612c097d2f15d6ba56f2d859aafd5aaaf5309c134a634b294d24219422829019fe3f07c0f49e73ca770e99cc390708db9b033e658c89862b8560a914d29050c9e93826e4c89591c22c43c840f01da3a0738e41ba334638c11762804d09411a220420590b01542a05309c1342404708c0cc1902f05c0b4140270440841001502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record002_frame006_links_0000 (interval_append _ 64 128 129 record002_frame006_links_0064 record002_frame006_links_0128))
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0562
    Papers.RationalityTen.SharedFrameCatalogue.group0562_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd63646b1ed8ceafe51428594049ae4b0a5652a494c4a2a4f926e930494a489236912485a3e11e28db3bc1a58d0466d2f19460a084f3270934497c4ac24d12208ee46722991048244021e80dd055229514209c84c424f11e88ac4322080fc07903a41a30c985842ac14f0a4050427413308f045c22010a06b823811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe2b69434499f4b4252fa9394729b6473a34d1808ad44d22210ec864429210906081d4059f64f9079430714aca345052410ecc73e38c1bc8d986a83421980c7861c2fc1748b5c54a29413008e43d81e40ee875c3a01c90e106ec3681ad0d3067432c1830be05982c01590a9052c28813d094048423411306d823811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3946aed45a52f7574ad156a8d4d89a132a634c09752d2574a89452724948c8fd1e2323e26d0d71a730e598b115f2ba568ab9542a2538a59482865009c9362584787e8f91ec3d0788ee1d63a0728e21be3686b8d019a30c608c017e2f85e8bc1722e05b8b615c228448690d01802f85a0b21602b8560aa150290330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5b1adf59aad50a9912fa5cc8e8ad13a23c428770d617c2884506e0a40b808fc1f3bd270cce197b245eeab55229d52ea35442814f29c9352624ae93d1ba2e4247f0d91a9344670c918d30e5fcbb9702ce574aa93c26645c8890d2104087e8f81ce3846e0d61561f43e0640c61702d8560aa150298520a2140270330640a8148240460881082003e0780e01502803c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6cf66a65d6505d157656d55f52b4cb4be4b04aa49e49548f48347846c4654574484264193fa39833d3313292f229228427927126525c25324a23d23522c21c20f1ea1e11c11ac17116b16516115d15715414f14914313d13613012511f10f10c10a1051000fb0f60e50e00da0d40ac08007f06406305b05a05505405305205105004f04d03303202a02902402302202102001f01e01c01501400f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame005_links_0000 record003_frame005_links_0064)
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc775f6af81792ae652fa9394709d549624612008ea46a230916089e446a1ed0e285d423a024fe87b037a1980ca86422f51594aae54429b14a0a3250827c93a89b64d226112bc90847122090046c435119e0ca462e30617a0b8c5a62c215c0a9852425b124883c3fa1ee0f007443861b90c305d82cc15106c023811a06b03501880c205c02d81680b205802b81580a803301900a8052024011808804202000f807803801500a003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame006_links_0000 record003_frame006_links_0064)
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0559.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0559.count (({ width := 8, code := 0xcecac9c7c3bfbebcb8b4b2b0afaeadacaaa9a8a6a5a4a19f9b9a9695938f8b89878685848381807f7d7c7b787672716d6b69686766656362615f5e5d5a5854535251504f4e4b4a494843403f3b3a36353231302f2e2d2c2a272622211e1d1c1b1a19181613120f0e0d0c0b0a090706050403020100 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0559.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0559.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame007_links_0000 record003_frame007_links_0064)
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0559
    Papers.RationalityTen.SharedFrameCatalogue.group0559_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c72d796a83509a68d1f688b429a08cfc678b3a97aeb695a32c895e2aca55b2a3d4e2a5e4fea76936c9854af252924690547923bd1d08e146d234d1988c345f22d515c8a444ea25911e78038e1bf4dba6a334099c8cc6632310971cb505882a714b0a3a50e26e93309904c125d12cc95a4a6250924c91848323d91d48de46c1f80f0873035a1978c705ca2d115c8aa453228a13d09ac4aa23611388283f81ee0f4075838c1b60d3865c3101720a9851024e11908584141ee0f007483881ba0d505802bc13809b03881bc0dc062030017c0680330190094048023006002c0140090030014008003 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record004_frame001_links_0000 (interval_append _ 64 128 142 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x297d109f93d676cde9ad346654c697d2de424698c1156224378630960ec187f4fc9f4bdb79af19dbbad752e9dd1b9a72ee35c4b7d6f4dc5b4b626b0d41a43125f2bad702cb586aed5b2ab54ca293f2704ba95927a494768dd1aa2f4588890f217422804fc9ef3ca77ceb9d636c6a8cf18d3005e8b39642c0574ab95129851c9f1312544708b10f21c428841031fa3dc788e71b234c628be1702dc588ac14e2885009c124244440870ce198328590b015c198320620941202301802c0500900c01402003 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record004_frame002_links_0000 (interval_append _ 64 128 142 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8bb88085e85284583382982280d80679574e7387227046ed6e46ba6ad66664e6346145f85ec5c05ae59959058858057857056256055154954653953152a5274b246c45443a41a3fe3f23c63b436034a3343162ff2f62cc2bf2b62ad2a529d29528d27f27d26e26626325624e24724421a20d2001ec1df1d81c11bb1b81b11a91a219a19118518217616e16a15f15815014d14613f13713012811f1131101040fc0f80ed0e60de0db0d50d10cd0c90c50c109409209108f08e08d07106f06e06c06b06a02a02802702502402301501301201000f00e } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record005_frame001_links_0000 (interval_append _ 64 128 142 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x7e1f1791de765d5745cf71dc46fdb26b1a768d9f67595649835f9795d1705b968591605795c56958559535494f5354c52547515444f92d4a1234791a46112439003e8f53c4ed3ace3380df374db364d7354d2344ce330cb320c6310c32dcb12b0a8290a22689725894248902388c22488214832087f1f47b1e8781d8741c8701b86b1a867194641845f1745c1685916057158551043f0f83c0ec3a0b02a0a4270982505c150501204410020060140300801 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record005_frame002_links_0000 (interval_append _ 64 128 142 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x92e448de318b2288922286a1784a057fdfa7d9f27c1e8795d6745cc71dc3705ba6d5b06b9ab6a1a56899d67197651936398c6298960d725b56858d5f57556545424f1374cd2f4b5254892147d1c4651644d0e43508415043fcfd3ecfa3b8e838cdf36cd9344ce334cb320c5308bf2e8b92d0b12c0ab2a4a7298a42889f27099258912408b22087208801f87d1ec7a1e4781dc761886017c5d1705b1344b1284811c460a82809c2509023054130481003c0e } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record005_frame003_links_0000 (interval_append _ 64 128 142 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x2995119f93d277ce29b535e64cc59292123ec768cf17a2bc4b88d0be1241b80efe5f8bdc7a6f2de2bbd770ec5d73a6748e65c9b92706dedb9b71676c918a3095eebb9742d3594ac553a9c528a3d4427c4ee9c934a654ba9692aa4848e8e518a2f44e8810d2183f079cee9c83746d0d099d334650c61862fa5d8b716a2bc55ca91462784d0981292464748a10f20a3f47b8e91c2370698ca1862fc5d0b415a2a45289d1042044007f0fc1f4338660ca18c31061050098128240460880a8130240400780e } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record005_frame004_links_0000 (interval_append _ 64 128 142 record005_frame004_links_0064 record005_frame004_links_0128))
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0626.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0626.count (({ width := 8, code := 0xa1a09e9d9c9a99989796959392918f8e8d8c8b8988878584838281807e7d7c7b7a797877767574737271706e6d6c6a69686766646362605f5e5d5c5b595857565554535251504f4e4d4c4a49484645444342413f3e3d3c3b3a3938373635343332312f2e2d2c2b2a292827262524232221201f1e1d1c1a1918171615131211100f0e0c0b0a090807050403020100 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0626.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0626.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record005_frame005_links_0000 (interval_append _ 64 128 142 record005_frame005_links_0064 record005_frame005_links_0128))
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0626
    Papers.RationalityTen.SharedFrameCatalogue.group0626_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2fadb6b195e2ba56ead3596b0d56aa753aa251b9c134666cc79852fa5d4af95929e4ec738c91762ac4f89310e1cc3585b0920fc1882102a023fe7e8fc1f43df7b8f61ea3d0798d4da4b44678ce198ac957caed572a9544a0d3b2714d89792a2464868e119a2e450724de1b7364690cd18c2ec5acb415b2ac53ca19382664b8941152124087d0f51dc38c6c8d219c320628bb1682c0550a7132258448860d01942c85607e0d81a0330640c41382504808c110120160280480800a01001802 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame001_links_0000 (interval_append _ 64 128 138 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0x32188bfdeaf176ba5cae36eb6daed163add5aa952a853a9b4aa4d1e89409dce66f3599cca5f2e964a651269248a411f8e46e33168ac52271288bf1f0f77a3cde0df6db69aed669b258ac3612f976b75b2cd62b057281389a4ca55248e44a150881401f4f075399c8e06b33998c6622f968ae552a148a24e2612c9248200f46c33160a446200e86830170b0542410078381a0a0401c0c05018080200 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame002_links_0000 (interval_append _ 64 128 138 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0x32188bfdeaf176ba5cae36eb6daed163add5aa952a853a9b4aa4d1e89409dce66f3599cca5f2e964a651269248a411f8e46e33168ac52271288bf1f0f77a3cde0df6db69aed669b258ac3612f976b75b2cd62b057281389a4ca55248e44a150881401f4f075399c8e06b33998c6622f968ae552a148a24e2612c9248200f46c33160a446200e86830170b0542410078381a0a0401c0c05018080200 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame003_links_0000 (interval_append _ 64 128 138 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2fb5bfb255eeb9d6fad158aaed53aa352ea05109ad31a61cbc96b2be55ca093b26646c6c8b313e244428790da1642883d052074087fcfe1f8bed7c4f75ebbca78ef0dde3b5762cc594323638c61892b4554a894ba9651a9bd3025a4a891d1fa2d4548850da174206d0d319f332630c11722c6558aa1462824f8979232404708a9031f23d0760e81c2358670c81882f45c8b015629c5009c11c234420820d61a43005d0800d81a0330640c41382504808c110120160280480800a01001802 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame004_links_0000 (interval_append _ 64 128 138 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0854.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0854.count (({ width := 8, code := 0xadacabaaa9a8a7a6a5a3a2a1a09f9e9d9c9b9a9998969594939291908f8e8d8c8a8988878685848382817f7e7d7c7b7a7978777472716f6e6d6a6867656463605e5d5c5a595857555453524f4d4c4b4948474442413f3e3d3c3a3938373432312f2e2d2c2a2928272624232221201f1e1d1c1b1a1918171614131211100e0d0c0b0a0807060503020100 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0854.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0854.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record006_frame005_links_0000 (interval_append _ 64 128 138 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0854
    Papers.RationalityTen.SharedFrameCatalogue.group0854_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb20b06afaaf3ad6ac7ab79d79c89c19b59a399497d96f9609518a888687686184b8378247f77d47c07aa79678176e75a7407297126fc62b61d61360b5fe5f35dd5d75cb5bc52750e5014ee4e14d34c449b48247746645944a43d42d41b40d3fc3ee36b35834d34133131f2fa2ea2d82c72b72ad2a12932862652552462322232132011f01cd1b51a819718717816b1561030bf07b07105d05c05b05a05805705605504303902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame001_links_0000 (interval_append _ 64 128 135 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x25393e4d92a4690e40852128420d82e0881603805ff791de76dd6749ce729c4701be6e9b66c5ac69da46859e66d765d1725c16e5b16759561575434fd3d4e9384d5324a9264911f46d1543d0a41d0540d00390e1378db360d5330c6300bb2e4b72d4b32c4a92909f2649624c902388720c811f8791d06f1a45a13049114390e0370d8340cc320c4300b01e0741c06c1906017058150441003c0e0340c02c0a024080140400c0200400 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame002_links_0000 (interval_append _ 64 128 135 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x32a993ac966483221902c7a56dab5559cac75602ae5560aab5522a7530c9644a9a4f525a91b485234d1628a044521e90d0857426211107a83641799f0cea66f3341984cb46513261914c7e55f2a194d4a4651828513f09a44b6254125891647d23791988c045b22b11446da35f1a78cfc66031f17f0bb85ba2cc15f0ab853c28f13f097449a23c11888a844621c10a878036e1a20c685f02d41570a384281a407b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame003_links_0000 (interval_append _ 64 128 135 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x35cda86d2b68db3f19c8ccd5642ad1540a8c53ba989490a3b513a84d23c8fa473a3451828ad44d219108483040e2034ff67e93ed9f18f6a7a53c99650b0056c2ac150ca5c51428393cc9be3ea1e30ecc73a38d1bc8d9866030e17e0ba05b22c715a8a9c524281138897c41e20810087e83e61ec0ef075c3a01c90e106ec3681ad0d3066032218a0c085e82e616c0b2854828813d09a84bc25012108c83d81aa07b03881740b805b02d01600ae05602a810c072025012008c04402000f807803a015008804001e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame004_links_0000 (interval_append _ 64 128 135 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x65f64f64564063462761959058858257b5735665595555485404df4cd4c24b44ab4a049748047046645a45544843e43442841e41540d38938137a37336836235134a3413382d72c32bb2ac2a129728f27826625f25224a24023622c21e21520d2051cb1c51bf1bc1b71b01a419d19618f18918418017a17316615e15715114b14313d13912711d11610e1070ff0f90f20d30b207206b05705605505405205105004f04003902502402302202001f01e01d01501101000f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame005_links_0000 (interval_append _ 64 128 135 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0x4da6933994c25f2e90c823f1e8ec7235198c45e170782c09fefd7dbe1ecf5793c5e0ef773b1d6ea74b71b6da6cb61aed56a34da4c6613017aba5c2d966b1582b558ab552a54ea652a912c94492411c8c4421908813f9f4f6793b9c4dc6b34198c8623096cae552913c9849228ec6c34180b4582b150a04e2612890401d0e06c34180b8582a140803c1c0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record007_frame006_links_0000 (interval_append _ 64 128 135 record007_frame006_links_0064 record007_frame006_links_0128))
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xccc65332418d2c5361fa99d482a2b50227b93b49764b425852b29534a6251527c93749824a524491b486a4191fe8ef47423851b46d63579a64cde659322153ca5651828213d09c24d125f12b093448823b919c88643221190007de3df1e78b805782a914a8a144e426212788f445621910407e03a81c30da06443001700b0055829e1480a084e826612508f045c2200d104a01c40c405d02e016c0b405902c015c0ac05501c80a804a024011808804202000f807803a015008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame001_links_0000 (interval_append _ 64 128 129 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd736a1b4ad9f8ce4666aa814eea6251da89d42691e47d239d1a68c1456a26911087643221490848304069fecfd27c63da9e94f2656c2a194b8a0e4f326f8fa878c3b31cf8e346f23661aa0d0866031e1870bf05b22c715a8a4850227112f88043e61ec0f207783ae1d00e487083761b40d686983301910c505e82e616c0b285802b21520a5851027a12f09404842340d504a01c40c405d02e016c0b405902c015c0ac05501c80a804a024011808804202000f807803a015008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame002_links_0000 (interval_append _ 64 128 129 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x33a660ca98eb17622abd52a9f524a31432594a69412624a48e91120a3e4768e11aa324588a51321e4368610a9bb3626accf198324594af95c2b0558a995029a528a39442824f89c1352644a8939242423f07b0f31de3b4750e71c83846f0db1b0354678cc1923045f0bb1702dc5b0b51682cc590b015e2b8568a31101ac2e0570ac1542a0530a41442804f0720a8128240460881082003e0780e81502003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame003_links_0000 (interval_append _ 64 128 129 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x36d6c0d69a634667eb4161abd55eaa5512754de9b1342664c69812ea5a4ae95128a4e4909152123a46e8d1189ca37a6dcd49a33385bcb49662c4580ae95a2ae550a894e296520a113f2784d09892e256418800fd1f23dc7a0f11dc3ac740e51c437c6c8d61a632c640c5184304600bf17c2f45e0ba1722e05b8ad1201bc3005b0b41642c0570ac1542a0530720a8128240460881082003e0780e81502003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame004_links_0000 (interval_append _ 64 128 129 record008_frame004_links_0064 record008_frame004_links_0128))
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb20b06afaad6ac7ab79c19a399496f9609518a888687686384b8378248108007f77ea7d47c079678176e7407297126fc6135fe5f35d75cb5bc52750e5014f04e14d34c44b34a449b49048247745944a43d41b40d3fc3ee34d33131f30b2fa2ea2d82c72b72ad2a12932862652552462232132011f01e21d51cd1c41b51a818717816b1570bf09407106205d05c05b05a05905805705605503902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame005_links_0000 (interval_append _ 64 128 129 record008_frame005_links_0064 record008_frame005_links_0128))
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc0f5faafb9796bb45cf29fd4d0a6051d289142295949b24b123090147523511848b044f22350f6871424a0d103e7f23ee1f18f5e6883359984c886323109628adc5652ab9514a6c52828c94209f24ea26d93489624a224a11bc8be4502200e306d83621a88cf46523171830bd05c62d31610ae0528281137891c46822210707f43dc1e00e8870c3721980c305d82cc0c904a01c40c405d02e016c0b405902c015c0ac05501c80a804a024011808804202000f807803a015008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame006_links_0000 (interval_append _ 64 128 129 record008_frame006_links_0064 record008_frame006_links_0128))
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x69b68868166f6646555c25b45a959758957d53052351e51851250a5014fa4f34ec4e64df4da4ce4c64be4ae4a749f4983f73e43dd3cb3bd3b034332f32b32331a30e3042f92f12e92e22da2d42bf2b42aa29128727c2702021f41ed1e51dc1cf1c51bb1b21aa1a519d19618117416b15314713d13212912211b11510e1090fd0f70f10eb0ae08806f06005b05a05905805705605505405303902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame007_links_0000 (interval_append _ 64 128 129 record008_frame007_links_0064 record008_frame007_links_0128))
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6e06d56cf6b76aa69e5e45d35ce5ba5af5a253d52a52551b5105054f84ee4e84df4d94ce4c94b24a749a48347946d4623a839b3943803723683012f22eb2e12d62c82bf2b42ad2a229d29428f27826a25f24923c2322281d01bf1b91b51af1a81a019819018817f17717016615f15714814013713012d12812211c1161101081010f90f30b409006f06005b05a05905805705605505405303902a02502402302202102001f01e01d01501000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame008_links_0000 (interval_append _ 64 128 129 record008_frame008_links_0064 record008_frame008_links_0128))
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1003.count (({ width := 9, code := 0x14ca4d1e87419fcce612e954a24d198b452251187c36170983c1607017ebedf2f2783b9d8e16f371b0d66a31d88c2602fd7abb5cadd6ab358abd56a953a813c9c4d239168943a190882401f8f87a3c1d8e4703719cca6330980be5e2e970b6592c15cac4f27128823c1d8e872381b8d86a34190a4482311084401f0f07438150803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame009_links_0000 (interval_append _ 64 128 129 record008_frame009_links_0064 record008_frame009_links_0128))
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1003
    Papers.RationalityTen.SharedFrameCatalogue.group1003_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x34dd1f44cdb31cb2edb9ee4b66d5b46a6a7a9aa4a89a0a7b9e2769ce719ba6b972549323d8e2338c1fb7ddf57ade6785c06f1ba6c9ac699a066d9965d9564d915fd785c5645855e569304a526479174450b41903400fe3ecf93ace6384d4340cc324c5304bd2e8b62cca527c992445d1644c10c3e0f43c0ec3a0e4380dc360c027088210801f0781d0701b068150400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record008_frame010_links_0000 (interval_append _ 64 128 129 record008_frame010_links_0064 record008_frame010_links_0128))
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a5ad2668fb461a22d0a681b3f19eacea58aac0d5e2ade5652ad9546a8f53f29793529974c2a5c92bc94a49ba48d2248f2477a3a11c28da469a33118a8be45ba2b91568a444ea25911e6c435a1a8cd22681339197cc986392b7957ca9c53c2961474a144f727213209824ba25992b494c49f24c124491048123d91d48de4691c10db46b43441978c7060e2f316e8b085722a914c8a284f426b12d893047821910507f03dc1e00eb071836c1a70cb86202f01690ac84d824e11908583f41ee0f007483881b60d5057826c0dc05f02000d806a03401980c80620270130094048023011004801800b00500240100060028010006002 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame001_links_0000 (interval_append _ 64 128 150 record009_frame001_links_0064 record009_frame001_links_0128))
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2bc574add5a6b2d61ab554ea75449a333663cc297d2ea59cac94f2763245d8ab13e24c438790d616c2483f0620840a808ff9fbbf07d0f7dee3d87a8f41e635d6b0d4da7349688cf99c3315b0b4164ac357caed59aa9544a4945a834f69d938a694bc9512323e4708cd172283b0744e49c13786dcd79a4334630c297d2ec5c0b59682c0558a793e2704cc971282464708a90f2124087e0f51dc3806c8d219c320610bb1682c0550a712c2183285607e0d81a8340660c81882704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame002_links_0000 (interval_append _ 64 128 150 record009_frame002_links_0064 record009_frame002_links_0128))
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0x2c761af56eb357aa5469f4aa1d067d3b9ccde693197caa4d2490c7a391a8bc52250d8642a0f0481401fafa7c3cde4f1783bddce974399cae471b85bede6cb61acd56a34da2cf6732d90c661b057cbb5cad962af572b156aa53a91449f4ea692e9549235188b44a210e8642209027d3e1e8f2783b9d8e873391c4de6d361a0ce653218cc2602f174b85b2a93c8839158a04e261289046200f8783a1c0d848180b050241006028100602 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame003_links_0000 (interval_append _ 64 128 150 record009_frame003_links_0064 record009_frame003_links_0128))
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0x35babd469747a1cf66f3394c3613037ebe5eaef74b95b6cd64b0d7ab95aabd52a54da652a8f44a15027b3a9c4ce6531984be5d218fc76391b8d4622d1483c1202ff7ebedf2f5793b1d2e772389bedc6cb559ecd6632992c8602f576b85b2cd60ad54a8d409d4d2612c944923916854220902803f9f4f67a3c9e0ec74391b0d6693419cca6431184c05f2b9448c39158a04e261289046200f8783a1c0d848180b050241006028100602 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame004_links_0000 (interval_append _ 64 128 150 record009_frame004_links_0064 record009_frame004_links_0128))
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0x2f578bb5d2e571b7db6d768ab552a550a75369749a3d1277399bcd66732984ba59299449a49229047e3b1b8cc5a2b1489c4a23007f3f1f4f87bbd5e6f071b85bedd6db69b0d669b3596c96331586c15f2ed6eb559ac560ae52289409d4e2693095492391a8b44a1d0a8441200fa773a9cce470379b4d66933998c8622f964ae552a148a04e2612c92481e8cc52200e86832180b8582a12088401e0e068281208038180a04018080200 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame005_links_0000 (interval_append _ 64 128 150 record009_frame005_links_0064 record009_frame005_links_0128))
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa89a82a7aa70a63a55a43a36a28a0393f93792e9239169098f88eb8dc8bc84783c82f82180e7fc7e67d57c47a079c79378377276375373e72a7166fb6f66e46d26bf6ab5d85cf5c65bc5ae59d58d5805704fa4ef4e44da4cc4bd4ac49e4904764704634554474394284184073f03e13d33c23b33a332e3233163082f82ea2dc2d02c12a72a029628627526725a2492392282051f61e51d71c91c21ba1ae1a01911831731651561331271181070fa0f10e60d90cc0be0b509f09506c05d04003603503403303203102702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame006_links_0000 (interval_append _ 64 128 150 record009_frame006_links_0064 record009_frame006_links_0128))
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x2564a994928a4ec999272324447d8710d21942e8570960ec1a829025ee3d77a2f31e2bbf772ec5d4b9c730e4dc7b88708dedbab6f6cad61ab350692d15a0ade5b4b59692ce594b15602bb4f69d93826c4cc9852ea5449c8f91c23345c8a10f219424824fb1f23d879cf09db344670cb992316608be1742da568ac1532a0528a313e2704cc95916226438841021fc3e87a8ef1d23906f0d71a231c610be1702c4560a91482784b893114200320560780d0198320620c01782604a090118220420480600b0140240400600a01001802 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame007_links_0000 (interval_append _ 64 128 150 record009_frame007_links_0064 record009_frame007_links_0128))
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
def record009_frame008_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x73973473072a72472071b71470e70466a65d65664d64163862e6236156015bf5b75ab5a259759058357757055655354c54754153c53753152a52451c51951350c5054fe44d43e43942e42241940e4013f739338a38037536a36335534934032a32331e31831230d3083012fb2f32ec2e52df2da2d426725b25224b23f23422821c20f1f81f21e91e21d81d01c71bd1b41a918d18417b17116515e15514e14413b13512911f1170f90f00e80dd0d10cc0c50c00bc0b60b109c09106c05d03e03503403303203103002702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record009_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record009) (record009.maps 8) (record009.inverseMaps 8) record009_frame008_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record009) (record009.maps 8)
      (record009.inverseMaps 8) record009_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame008_links_0000 (interval_append _ 64 128 150 record009_frame008_links_0064 record009_frame008_links_0128))
theorem record009_frame008_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 8 :=
  of_group record009 8 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record009_frame008_indices record009_frame008_graph record009_frame008_links
def record009_frame009_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2bdd73adf5a2b155daaf546a5d4098d30e5e4b595f2ae5249d9332362cc4f89110a1e4368610a20f41481d021ff3f87e2fb5f33dd7aef29e3bc3778ed5d8b3c66ccc596b28646c798c31257eadd5a2ad554a894da9651a9f93aa6f4cc9812d25048e8fd16a2544286d0ba103846e8da1ab34c67cca98c3045c8b59672c6570ab1542945049f12a2464808e115220424818ff1f23d0770e81c234c670c81882f45b0b015629c5009c11a2083485d0800d81a8340660c81882704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record009_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record009) (record009.maps 9) (record009.inverseMaps 9) record009_frame009_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record009) (record009.maps 9)
      (record009.inverseMaps 9) record009_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame009_links_0000 (interval_append _ 64 128 150 record009_frame009_links_0064 record009_frame009_links_0128))
theorem record009_frame009_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 9 :=
  of_group record009 9 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record009_frame009_indices record009_frame009_graph record009_frame009_links
def record009_frame010_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0851.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0851.count (({ width := 8, code := 0xb8b7b6b4b3b2b1afaeadaaa9a8a6a5a4a3a1a09f9d9c9b9998979694939291908f8d8c8b8a8887868584838281807f7e7d7c7b7a7877767574737271706e6d6c6b6a686766646362615f5e5d5c5b5a59585655545251504f4e4d4c4b4a49484645434241403f3e3d3c3b3a39383635333231302f2d2c2b2a292825221f1c1a18171615141311100f0e0d0c0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0851.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record009) (record009.maps 10) (record009.inverseMaps 10) record009_frame010_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0851.localPairCheck (smallEmbedding record009) (record009.maps 10)
      (record009.inverseMaps 10) record009_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame010_links_0000 (interval_append _ 64 128 150 record009_frame010_links_0064 record009_frame010_links_0128))
theorem record009_frame010_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 10 :=
  of_group record009 10 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0851
    Papers.RationalityTen.SharedFrameCatalogue.group0851_facts record009_frame010_indices record009_frame010_graph record009_frame010_links
def record009_frame011_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0848.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0848.count (({ width := 9, code := 0x237198bc5225108742e130681c05fefc7d3e1ecf378bb9d8ea74395c6e16fb71b4d76b351a4cf66b2d92c66230580bf5f2f578bb5d2e570b75b2d566b2582bd5cad562ad54a853a9546a14f27134974aa4d208e46a31168a44a1d0a82401f8f6793b9d0e672389c0de6e369acd46733194c86331184c05f2f174b85a2c958aa5429948a04f27134984b241147a35140984a2411888421f0f074381b0d048180b050241006028100602 } : Fields).get c.val)
theorem record009_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 11) (record009.inverseMaps 11) record009_frame011_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0848.localPairCheck (smallEmbedding record009) (record009.maps 11)
      (record009.inverseMaps 11) record009_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame011_links_0000 (interval_append _ 64 128 150 record009_frame011_links_0064 record009_frame011_links_0128))
theorem record009_frame011_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 11 :=
  of_group record009 11 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0848
    Papers.RationalityTen.SharedFrameCatalogue.group0848_facts record009_frame011_indices record009_frame011_graph record009_frame011_links
def record009_frame012_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0366.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0366.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0366.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0366.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0366.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0366.localPairCheck (smallEmbedding record009) (record009.maps 12) (record009.inverseMaps 12) record009_frame012_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0366.localPairCheck (smallEmbedding record009) (record009.maps 12)
      (record009.inverseMaps 12) record009_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame012_links_0000 (interval_append _ 64 128 150 record009_frame012_links_0064 record009_frame012_links_0128))
theorem record009_frame012_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 12 :=
  of_group record009 12 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0366
    Papers.RationalityTen.SharedFrameCatalogue.group0366_facts record009_frame012_indices record009_frame012_graph record009_frame012_links
def record009_frame013_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0364.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0364.count (({ width := 8, code := 0x9594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record009_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0364.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record009) (record009.maps 13) (record009.inverseMaps 13) record009_frame013_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0364.localPairCheck (smallEmbedding record009) (record009.maps 13)
      (record009.inverseMaps 13) record009_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame013_links_0000 (interval_append _ 64 128 150 record009_frame013_links_0064 record009_frame013_links_0128))
theorem record009_frame013_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 13 :=
  of_group record009 13 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0364
    Papers.RationalityTen.SharedFrameCatalogue.group0364_facts record009_frame013_indices record009_frame013_graph record009_frame013_links
def record009_frame014_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0306.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0306.count (({ width := 8, code := 0xf4f3f2f1f0efeeedecebeae8e6e4e2e0dedcdad7d6d4d2d0cecccac8c6c3c2c0bebcbab8b6b4b2b0afaeadacaba9a7a5a3a19f9d9b99969492908e8c8a88868482807e7c7a7876747271706f6e6d6c6a68666462605e5c5a5958575655545352514f4d4b4947464544434241403f3e3c3a383634333231302f2e2d2c29282221201f1e1d1c1b1a19181716100a090807060504030201 } : Fields).get c.val)
theorem record009_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0306.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0306.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0306.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0306.localPairCheck (smallEmbedding record009) (record009.maps 14) (record009.inverseMaps 14) record009_frame014_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0306.localPairCheck (smallEmbedding record009) (record009.maps 14)
      (record009.inverseMaps 14) record009_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame014_links_0000 (interval_append _ 64 128 150 record009_frame014_links_0064 record009_frame014_links_0128))
theorem record009_frame014_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 14 :=
  of_group record009 14 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0306
    Papers.RationalityTen.SharedFrameCatalogue.group0306_facts record009_frame014_indices record009_frame014_graph record009_frame014_links
def record009_frame015_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17dabdb5e22ed1748b915c02dc16bab4b52828f5448a1450227cd3c89d44e1a6c926a91e482a3c51c08cc45d22a512a88343c2181092835411a0490027ef3ef1f44f9a7b73d01e20eec6443179868c165fc2f61778b9e5bf29d949ca2450227a139c9ae4c925e12a092c48423a119c8b444c21f90c884a4142020fc87ca3d91a98cf464e3171840be45d42db1660af856229d14509e04da260129091c47422010787f43e21e40eb071836a1a80ce064030a1790b6854c28012d090845420e0f907483781a80c9055826c0dc05f02000d806a03401980c80620270130094048023011004801800b00500240100060028010006002 } : Fields).get c.val)
theorem record009_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 15) (record009.inverseMaps 15) record009_frame015_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 15)
      (record009.inverseMaps 15) record009_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame015_links_0000 (interval_append _ 64 128 150 record009_frame015_links_0064 record009_frame015_links_0128))
theorem record009_frame015_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 15 :=
  of_group record009 15 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record009_frame015_indices record009_frame015_graph record009_frame015_links
def record009_frame016_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x68167c67566f66866065965264a6415b45ad5a059558c58057656b55f55251250b4fe4f34e84dc4d44cb4bf4b04ad4a74a149b49448d48748047947147046a46345c4563a239738b37d37436a35d35434c2f32e82dc2cd2c42bc2af2a629c28e28828227b27526e26826225b25424f24924323b2351ea1df1d51ca1c21b81af1a719d19418f18717c17617216e16816315d15014613c13813112d12511a11210d1071020fe0fa0ee0e40da0d30d00cc0c70c20be0bc0bb0a309706c05d03e03503403303203103002702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record009_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record009_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 16) (record009.inverseMaps 16) record009_frame016_indices (Fin.ofNat record009.n i)) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem record009_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record009) (record009.maps 16)
      (record009.inverseMaps 16) record009_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 150 record009_frame016_links_0000 (interval_append _ 64 128 150 record009_frame016_links_0064 record009_frame016_links_0128))
theorem record009_frame016_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 16 :=
  of_group record009 16 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record009_frame016_indices record009_frame016_graph record009_frame016_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (Fin.cases (record009_frame008_supported hcells) (Fin.cases (record009_frame009_supported hcells) (Fin.cases (record009_frame010_supported hcells) (Fin.cases (record009_frame011_supported hcells) (Fin.cases (record009_frame012_supported hcells) (Fin.cases (record009_frame013_supported hcells) (Fin.cases (record009_frame014_supported hcells) (Fin.cases (record009_frame015_supported hcells) (Fin.cases (record009_frame016_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x93e93592c9209139068f58e88d98bf84683a82d81f80c7f97e37d27c27a379b79078076f76075073b7277135d95d25c95bf5b15a059058357355d4fb4f24e74dd4cf4c04af4a149347b47546d46045244443642541540432d3203133052f52e72d92cd2be2a029628627526725a2492392282071f81e71d91cb1c21ba1ae1a019118317316515613512911a1090fc08b07606c05d05705605505405304003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame001_links_0000 (interval_append _ 64 128 129 record010_frame001_links_0064 record010_frame001_links_0128))
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9d79c89c19b59a399498596f9609498c68b48a989b88987986784e83a81f8108007f77ea7d47c07ac79678162b61d61360b5fe5f35e55d75cb5b454353352851f5115044f44e44d64bf4b34a449b49048247746945944a36b35834d34133131f30c2fa2ea2c72b72ad2a12932862752652552322232132011f01e21d51cd1c41b51a819818717815514313312311309107806e05f05905805705605504003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame002_links_0000 (interval_append _ 64 128 129 record010_frame002_links_0064 record010_frame002_links_0128))
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x33dceb37cd331cbb2ac9720c66f9bd6f1bb6e8b8edbb4ac9afebaadab2ab6a9a96a0a66928f63a8de348c62e8aa2487a177f9fb7e1f57c5ed7a1de751c7711c16f9b96d5b16b1a567957551515394a519414e531491214791a4591243908408f53c0eb3a0e437cdb35cd333ccb31cbf2dca7280992508d1845714047104400fc3e0f4370cc270842007c1e074120441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame003_links_0000 (interval_append _ 64 128 129 record010_frame003_links_0064 record010_frame003_links_0128))
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xa4d51d2885424a024f8a7893a49c14d9a4c9236902477a3791948b8453a24d10887542ea1190648204079ff8fd87db32398c8c3a60e2ff97bcbc25d22e116d0a7c52a28a94149ee4ea26d133097e4b1252924c902471232115c89243c2178d4067432418a8c185ee2e816c8b2856229d14509e04da260129091c47422210887fc3e41e50eb071836a1a80ce064030a1790b6855428412f0910458122078037017c0b205802b81580aa04001b009c04202000f807803a012008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame004_links_0000 (interval_append _ 64 128 129 record010_frame004_links_0064 record010_frame004_links_0128))
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x18ac461b0982c05faf97abbdc6dd6bb4592c15cac5529d4ba4d1e89419f4ee71358a4461d0b8441604ff7e3e1e4ef763a5cae16eb65aad066b2d92c661b017aba5ba5d2a9348a39168842a08fc7d3e1ecf2773a9cce26e361a8d0663218cc4612f974b6592b94ca04d2511c6e361a8d05c2d160ac542914088381b0d06430110803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame005_links_0000 (interval_append _ 64 128 129 record010_frame005_links_0064 record010_frame005_links_0128))
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0291.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0291.count (({ width := 8, code := 0x807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0291.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0291.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0291.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0291.localPairCheck (smallEmbedding record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0291.localPairCheck (smallEmbedding record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame006_links_0000 (interval_append _ 64 128 129 record010_frame006_links_0064 record010_frame006_links_0128))
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0291
    Papers.RationalityTen.SharedFrameCatalogue.group0291_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xac855a2a81518a775312941476a27505a52526a921487a3f51d48d746222c112a88843b21910a4842418207d01a7fb2ca1600ad85582a194b8a38507279935c82a4011f68f6c7923b61d18e406f83611aa0d0866031e1870bf05d62d9163883c4102010fd07cc3d81e50ef075c3921c20dd86d035a1a60cf86603221810bd05cc2d81650b005642a414b0a204f426c12f094046022210a08183f0122078037017c0b205802b81580aa04001b009c04202000f807803a012008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame007_links_0000 (interval_append _ 64 128 129 record010_frame007_links_0064 record010_frame007_links_0128))
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
def record010_frame008_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5a159c59158b57e57956f56155a5474f34ef4e54e14d54ce4c24b44ad49949548f48347846c46545944a43c36836135c35034a34033332b32130e2ba2b42af2a529f29528827d27426025c25324a23d23522c21e21120318b18718117c17717116c16616115715414f14914313d13813212d12311d11611110e10c10a1051000fb0f60f00ea0e50d80d20cd0c70c308307006705805205105004f04e03f03602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record010) (record010.maps 8)
      (record010.inverseMaps 8) record010_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame008_links_0000 (interval_append _ 64 128 129 record010_frame008_links_0064 record010_frame008_links_0128))
theorem record010_frame008_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 8 :=
  of_group record010 8 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record010_frame008_indices record010_frame008_graph record010_frame008_links
def record010_frame009_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x59058858257b57356655f5555485394f04e84e04d94d04c54ba4ae4a349248c48548047847046645c45544838938137a37336836235734a3413312e92e02d82d12c62be2b22a429a28a28427d27827026625f25424a2401cb1c51bf1bc1b71b01aa1a419d18f18918418017a17316c16615e15114b14313d13913312c12712311d11610f1070ff0f10e90e10dc0d708506f06805905305205105004f03d03602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record010) (record010.maps 9)
      (record010.inverseMaps 9) record010_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame009_links_0000 (interval_append _ 64 128 129 record010_frame009_links_0064 record010_frame009_links_0128))
theorem record010_frame009_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 9 :=
  of_group record010 9 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record010_frame009_indices record010_frame009_graph record010_frame009_links
def record010_frame010_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x5d25ce5c45bb5b25a859d59258657b52e52351650a4ff4f54e84db4ce4c24bc4b34aa49f49949248847f47539639238837e37336735d35434a33f2f22e72da2cc2bf2b22a729c29228628027726e26225924f2462402391c11bb1b41ae1a619e19618e18617d17917216b16515d15514f14713c13813312e12712311e11a11410d1071000f90f30e90e40de0d90d308f07706d05e05805705605505404003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record010) (record010.maps 10)
      (record010.inverseMaps 10) record010_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame010_links_0000 (interval_append _ 64 128 129 record010_frame010_links_0064 record010_frame010_links_0128))
theorem record010_frame010_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 10 :=
  of_group record010 10 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record010_frame010_indices record010_frame010_graph record010_frame010_links
def record010_frame011_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xb125802bb95b6ac7559aa81518a7b530a6993289824b7a56d28e934490243d1ea8ee473a3811b28d2465a31117a8b63639adcd4c69434219d4cc464f31e188cae45622a894fca5e52028693e89ce4ce26393009724b2256129493c4972480dfc6d43571a08cb06323041780b685722a914c8a284f426b12d893047821b10607f83e01e20eb071836c1a70cb86202f01690ac84e025211b08683fc122078037017c0b205802b81580aa04001b009c04202000f807803a012008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record010_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 11)
      (record010.inverseMaps 11) record010_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame011_links_0000 (interval_append _ 64 128 129 record010_frame011_links_0064 record010_frame011_links_0128))
theorem record010_frame011_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 11 :=
  of_group record010 11 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record010_frame011_indices record010_frame011_graph record010_frame011_links
def record010_frame012_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x5d45cc5c65c05b55ae5a159658d57953553152a52251b50f5054fa4ee4da4d44d04cb4c54c04bb4b54af4a93fa3f53ee3e93df3d73cc3c03b53a035735434f34633f33432a3213122fd2f82f42f02eb2e52e02d92d32cd24924023322721d2132081fb1f01db1d51cc1c41b91b11a419919117a17116615d15314b14613e13412c12111510c1010eb0e30d60cd0c308507406b05d05705605505405303e03502702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record010) (record010.maps 12) (record010.inverseMaps 12) record010_frame012_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record010) (record010.maps 12) (record010.inverseMaps 12) record010_frame012_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record010) (record010.maps 12) (record010.inverseMaps 12) record010_frame012_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record010) (record010.maps 12)
      (record010.inverseMaps 12) record010_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame012_links_0000 (interval_append _ 64 128 129 record010_frame012_links_0064 record010_frame012_links_0128))
theorem record010_frame012_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 12 :=
  of_group record010 12 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record010_frame012_indices record010_frame012_graph record010_frame012_links
def record010_frame013_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x66765b65564a63f63762c6206136035bd5b45aa59f59658e58157556d55855254b54554053b53653052952345044143a43142441b4114043fa3e939638d38137836c36535834c34333032932231c31731130c3073002fa26525925124923d23222621920c1f21e91e21d81d01c71bd1b41a918f18617c17316715e15514e14413b13512911f1170fb0f10ea0df0d308b07606c05d05705605505405303e03502702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 13) (record010.inverseMaps 13) record010_frame013_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 13) (record010.inverseMaps 13) record010_frame013_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 13) (record010.inverseMaps 13) record010_frame013_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record010) (record010.maps 13)
      (record010.inverseMaps 13) record010_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame013_links_0000 (interval_append _ 64 128 129 record010_frame013_links_0064 record010_frame013_links_0128))
theorem record010_frame013_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 13 :=
  of_group record010 13 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record010_frame013_indices record010_frame013_graph record010_frame013_links
def record010_frame014_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x71a7117076fa6f06e66d66ca6bf6aa62261960e6005f45e85d55c75b95a059758e58657e57656e56655e55542841f4144063fa3ee3db3cd3bf3a632c32331930c3022f82e82dc2d12bc2b42ab2a329b29328b28327b2721fa1f31ec1e61df1d81d11ca1c31b71b01a81a119919018818117916716015915114a14513e13612f12711e11610f1070f50ee0e70df0d809107806e05f05905805705605504003602702102001f01e01d01201101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record010_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 14) (record010.inverseMaps 14) record010_frame014_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 14) (record010.inverseMaps 14) record010_frame014_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 14) (record010.inverseMaps 14) record010_frame014_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record010) (record010.maps 14)
      (record010.inverseMaps 14) record010_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame014_links_0000 (interval_append _ 64 128 129 record010_frame014_links_0064 record010_frame014_links_0128))
theorem record010_frame014_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 14 :=
  of_group record010 14 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record010_frame014_indices record010_frame014_graph record010_frame014_links
def record010_frame015_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x44988d0fe1f4368670b61241e81cf59e9bcc792f05dcbb274ae75c5b846fcde1b9b6d6d2d89acb525bab616aace590b015b2af548a493125d4b89552924c48a8f91ba274428690aa0f416818ff1f63de688cf99a32a63cc51852fe5ecb996c2ce580ac9542985109e92e24c47c8d11421e428810fc1ea3c0740e01b2324618bb16c2c03f86d0c81582804f09c1342603e0680981082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record010_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record010) (record010.maps 15) (record010.inverseMaps 15) record010_frame015_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record010) (record010.maps 15) (record010.inverseMaps 15) record010_frame015_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record010) (record010.maps 15) (record010.inverseMaps 15) record010_frame015_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record010) (record010.maps 15)
      (record010.inverseMaps 15) record010_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame015_links_0000 (interval_append _ 64 128 129 record010_frame015_links_0064 record010_frame015_links_0128))
theorem record010_frame015_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 15 :=
  of_group record010 15 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record010_frame015_indices record010_frame015_graph record010_frame015_links
def record010_frame016_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x42f85309a0fc1982303202bfc7e4f31e43c0772ecdd5ba673ae51c3b816f8dddb836a6c8d7dad3535c0b696a2cd58ab055d2b154ea6d3c2754de9a13025c4aa9312323b46c8c51622543c8690a20e4106b0d299f338658c898c3085f0b816a2ca57cac15129851ca013325c4908e917222430831001f03c8768e71c2350668c617c2e03f86b0c61582804f09c1342603c06809c1082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record010_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 16) (record010.inverseMaps 16) record010_frame016_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 16) (record010.inverseMaps 16) record010_frame016_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 16) (record010.inverseMaps 16) record010_frame016_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record010) (record010.maps 16)
      (record010.inverseMaps 16) record010_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame016_links_0000 (interval_append _ 64 128 129 record010_frame016_links_0064 record010_frame016_links_0128))
theorem record010_frame016_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 16 :=
  of_group record010 16 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record010_frame016_indices record010_frame016_graph record010_frame016_links
def record010_frame017_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0376.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0376.count (({ width := 9, code := 0x1108743215088341202fe7dbd5e6f177bb5d6e97338dc0dd6db65aed569b459ecd5f2f174b85b2d164af562a546a14fa7536994ba51228e45a250e8541a04fe7d3d9b4d86b351a4d0673298cc05f2f174b85b2d160ac52281389a4b251249047231148842200f074381b8d45a2b150a04c251208c44200f874361a0c8602e12088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record010_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record010) (record010.maps 17) (record010.inverseMaps 17) record010_frame017_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record010) (record010.maps 17) (record010.inverseMaps 17) record010_frame017_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record010) (record010.maps 17) (record010.inverseMaps 17) record010_frame017_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record010) (record010.maps 17)
      (record010.inverseMaps 17) record010_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame017_links_0000 (interval_append _ 64 128 129 record010_frame017_links_0064 record010_frame017_links_0128))
theorem record010_frame017_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 17 :=
  of_group record010 17 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0376
    Papers.RationalityTen.SharedFrameCatalogue.group0376_facts record010_frame017_indices record010_frame017_graph record010_frame017_links
def record010_frame018_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1045.count (({ width := 11, code := 0x36a6ccd7dac352698d199fb39664c3d853035f8bd577ae95c2b6568acb592b0d5dab7560aad5329e47a8e118a2a4448690aa0e4107fcee1d83a2728e19bd3706c8d61a433e674cb98f314608bf17a2e64e89c1352664bc959282484808d118226438859062023f87c8ee1d4398710dc1b0358688cc1923105f8bc16e2b0540a413e268378610b41382404708c1142203a06609c1082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record010_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record010) (record010.maps 18) (record010.inverseMaps 18) record010_frame018_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record010) (record010.maps 18) (record010.inverseMaps 18) record010_frame018_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record010) (record010.maps 18) (record010.inverseMaps 18) record010_frame018_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record010) (record010.maps 18)
      (record010.inverseMaps 18) record010_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame018_links_0000 (interval_append _ 64 128 129 record010_frame018_links_0064 record010_frame018_links_0128))
theorem record010_frame018_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 18 :=
  of_group record010 18 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1045
    Papers.RationalityTen.SharedFrameCatalogue.group1045_facts record010_frame018_indices record010_frame018_graph record010_frame018_links
def record010_frame019_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x43385b0a610c1d82d04a064037f4f41e5bc4778ed9d73a7744e61c6b87706dfdbbb746d6d91af3555aab3d64ac1570ac5552a553ca493726b4c89792aa4e49090d1fa3545e8ad13a1f432835029ff3f668cce196326630c197f2f25c8b29622bc55caa94e28c5049d92d24c4788c10f214410800f91e83ac720e01b833c640c11722c43885f0b213c2484808e118228370620981082003e0780e8120220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record010_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record010) (record010.maps 19) (record010.inverseMaps 19) record010_frame019_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record010) (record010.maps 19) (record010.inverseMaps 19) record010_frame019_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record010) (record010.maps 19) (record010.inverseMaps 19) record010_frame019_indices (Fin.ofNat record010.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record010_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record010) (record010.maps 19)
      (record010.inverseMaps 19) record010_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record010_frame019_links_0000 (interval_append _ 64 128 129 record010_frame019_links_0064 record010_frame019_links_0128))
theorem record010_frame019_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 19 :=
  of_group record010 19 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record010_frame019_indices record010_frame019_graph record010_frame019_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (Fin.cases (record010_frame008_supported hcells) (Fin.cases (record010_frame009_supported hcells) (Fin.cases (record010_frame010_supported hcells) (Fin.cases (record010_frame011_supported hcells) (Fin.cases (record010_frame012_supported hcells) (Fin.cases (record010_frame013_supported hcells) (Fin.cases (record010_frame014_supported hcells) (Fin.cases (record010_frame015_supported hcells) (Fin.cases (record010_frame016_supported hcells) (Fin.cases (record010_frame017_supported hcells) (Fin.cases (record010_frame018_supported hcells) (Fin.cases (record010_frame019_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa87a80a78a6ca5fa51a3fa32a22a0f93e93592c9209139068f58e88d98c684583782a81c8097f77e07cf7bf7a879b79078076f76075073b7277137006eb6d96c66b36a05d95d25c95bf5b15a05905835735644fa4ef4e44da4cc4bd4ac49e49048047546d4604524444364254154043f53e43d63c53b63a632d3203133052f52e72d92cd2be2ac2a029628627526725a24923922821a2071f81e71d91cb1c21ba1ae1a01911831731651561460b405c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame001_links_0000 (interval_append _ 64 128 153 record011_frame001_links_0064 record011_frame001_links_0128))
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb31b27b20b14b06afaaecad6ac7ab79d79c89c19b59a399498596f9609518c38b18a889888687686484b8378248108007f77ea7d47c07ac79678176e7567407297126fc62b61d61360b5fe5f35e55d75cb5bc54053052751c50e5014f14e14d34c44b34a449b49048247746945944a43d42941b40d3fc3ee36b35834d34133131f30c2fa2ea2d82c72b72ad2a12932862752652552462322232132011f01e21d51cd1c41b51a819818717816b0bf05e05d05c05b05a05905805705605502602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame002_links_0000 (interval_append _ 64 128 153 record011_frame002_links_0064 record011_frame002_links_0128))
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x394e478ee2f88e1781df779dd73dceb37cd331cbb2ac9720c6ef8bd2f0baee6b86d8b3ec6b02baadab2ab6a9a96a0a6692a36839f2759ca6e8f63a8de348c62e8aa2487a197f5fa7ddf37bdeb795db745ca711c16f9b96d5b16b1a56799963d886057e5e957551515394a519414e5314a9244851e469164490e421023f4f53c0eb3a0e437cdb35cd333ccb31cbf2dcb01b4461144410c42104400fc3e0f4260942408c220842007c1e074110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame003_links_0000 (interval_append _ 64 128 153 record011_frame003_links_0064 record011_frame003_links_0128))
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc2a60eb03d806bf55f72f89796bb45cf2a6d516a7f53a29a14c0a5051d289142297c4b5a56529093649624652028ea46a230916089e446a1ed0e285f424a0d103e8073f91f70f8c7af3539a64d1067c3359984cac6443191884b4c5972c515ecadc5652ac1514a6c52828c94209f24ea26d93489884b1251125090446f22f91408803ad1cd8e306f636c1b10d4867a32918b8c185e82e31698b085702a814a0a044de25912388d044420e0fe87b83c01d10e186e43561980c305d819205e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame004_links_0000 (interval_append _ 64 128 153 record011_frame004_links_0064 record011_frame004_links_0128))
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x353d434dd2b47d133dcdb31cb2f3bc2edbaae7b92e0b66d5b46aeaaaa6a8a9ea6a93a26829ee789da739c66e9ae6397254932418f6388ce307fdfd7edf97ddf57c5eb799e1711c2701be6f1ba6cdac699a066d9965d9564d916217f5e17159d645855e569384d1304b5294991f45d1142d0640d003f8fb3e4f33ace6384d8350d0330c9314c12f4ba2d8b32b4a527c991743f0f83d0f03b0e8390e0370d823088210801f0781d0701b068110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame005_links_0000 (interval_append _ 64 128 153 record011_frame005_links_0064 record011_frame005_links_0128))
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x2288962287e1c866158460d825e8795e277ddc765d674dd0735b76d1b16b9ab6a1a367999651926418e6318a6218660d805f57a5e1765d17256557555535454f53149519434b92c4a928499244891f4711945914449104390c42505404fd3ecf93dcf53ccd7350d1338cb320c5300bb2d8b22c0ae2b0aa2a0a62889e2689624c902348b22086210822007e1f0771c86d13c380dc360d4340cc320c4300bc2007c1e0741c06c1a0641805c110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame006_links_0000 (interval_append _ 64 128 153 record011_frame006_links_0064 record011_frame006_links_0128))
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x257956539464f9364991a439021484a108360b8220680e017fdea79de4785de76dd8749ce729c8719c4709c06f9bb6d9b16b1a6691a16799b5d9745c9705b96c5a5655855d51d4550d414fd3d4f1384d5324b92c4a928499244851b4550f4250741503400e4384de36cd8354d3330c6300bb2e4b72d4b32c4af2a4a427c99258932408e22c8921c8520c811fc791d06f1303a0e4380dc360d4340cc320c41f0781d0701b0681906017058110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame007_links_0000 (interval_append _ 64 128 153 record011_frame007_links_0064 record011_frame007_links_0128))
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0336.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0336.count (({ width := 10, code := 0x1dc769d8759d4749d0739cc729aa6a1a6691a26819f6799d67187611815f97b5e1755c96f5b16a5a166591625815f5755b56556551525414f4d9344c9304b92c4a5274952343d0d42d0941d0541102400fe3ecf93dcf53ccf13bcec3a4e6390e2380de370c12f8bb2e0b52c8b02b0a8290a02789c26898258942408c220842047e1ec791dc751cc711bc6d1ac661845c104340cc320c4300bc2e0b42c0ac1e0741c06c1a0641805c160541003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0336.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame008_links_0000 (interval_append _ 64 128 153 record011_frame008_links_0064 record011_frame008_links_0128))
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0336
    Papers.RationalityTen.SharedFrameCatalogue.group0336_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0273.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0273.count (({ width := 10, code := 0x1e578de177ddd76dd975dd574db36c5af6b5ab6a5a869da6695906358a61d846057d5e5755c56f5b56b5a56759564589605795b56557555544ed394dd354cd314b92c4a928451124410e4310a42105408ff3f0fa3e0f63d0f23c0ed3a8e7394e3384df374c22fcbc2e4b62ccb12b4a9294a127c9d26c9925c952448d224852087f1f07a1e0761d0721c06e1b0671885d104340cc320c4300bc2e0b42c0ac1e0741c06c1a0641805c160541003c0e0340c02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0273.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame009_links_0000 (interval_append _ 64 128 153 record011_frame009_links_0064 record011_frame009_links_0128))
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0273
    Papers.RationalityTen.SharedFrameCatalogue.group0273_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbe85eaaefd762ba05c6adf56d8b595a7a935474a2150928093e29e24e9270536a92f48c23fd1d88db463a2d5148890442a1d50ba846419208101e7fe3f61f6cfa47be3d49e40efa76b32398c8c3a60e2ff97bcbc25d22e116d8a7652728914089e84e726b93249784b2252924c902471232115c89243c217909882e4071fa8f9c7b635019d0c9062a30617b8ba05b22ca15f8ac453a28a13c09b44c025212388e846222210887fc3e41e50eb071836a1a80ce064030a1790b6859019005e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame010_links_0000 (interval_append _ 64 128 153 record011_frame010_links_0064 record011_frame010_links_0128))
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
def record011_frame011_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x5a2b39662cad8ab07602bdd73ad74828cd14a1d4167e4f89e73ae7149991921a3ec728d11862dc518910ea1642683b04603c007f2fc1f33df79cefdd9ba56aad35a3340676cc595b27644c5d6fad2592b0d5e2b355caa151a9b524a1d402784e0999302584a892d222364548810a9e03a872ce31c03706ccd71a9342664c71863005f0ba16e2d0594ae9572965009c13024e46c8990f20e4047e8f61e43b0488520a21402784e09a1302584a092098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 11)
      (record011.inverseMaps 11) record011_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame011_links_0000 (interval_append _ 64 128 153 record011_frame011_links_0064 record011_frame011_links_0128))
theorem record011_frame011_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 11 :=
  of_group record011 11 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record011_frame011_indices record011_frame011_graph record011_frame011_links
def record011_frame012_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x1afd6eaf53a7d2e8f439fcee2b1186c260b017ebe5eaf170b6daacd62af56aad52a7d2e9347a25067d3b9c4d6672f964a64f258a4461d0b8441604ff7e3e9e2ee75b9dc6df6db5da6d166b2d92c661b017aba5bad562ad54a9946974aa4d228e45a210a823f9f8fa7c3d9e4ee75399c4de6e361a8d0663218cc4612f974b6592b9547433190c4602f170b4582b15084401f0f074381b0d0643010078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record011_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 12) (record011.inverseMaps 12) record011_frame012_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 12)
      (record011.inverseMaps 12) record011_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame012_links_0000 (interval_append _ 64 128 153 record011_frame012_links_0064 record011_frame012_links_0128))
theorem record011_frame012_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 12 :=
  of_group record011 12 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record011_frame012_indices record011_frame012_graph record011_frame012_links
def record011_frame013_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x43c8710ce1842b8510920fc1c830f41e5bc7784ef9dd3b5762eb5d4b87700de1b8b696c8d79ab35169ad25a0b3c668cbd93b2363cc59893065febe978ae8534a5547a895069f53ca734da9a524a4347a8d91822a44c8810d217428831032003f47d0f89eb3ca788ec9d239e724e19903105fcbb16d2ca580ab94f296528a093d26a4c4949252424648a90d21040c7e0f51de39c708da1a8334650c417a2e83904808e118228440861082084007e08c1102104007c0f01d03806c0d01102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 13) (record011.inverseMaps 13) record011_frame013_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record011) (record011.maps 13)
      (record011.inverseMaps 13) record011_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame013_links_0000 (interval_append _ 64 128 153 record011_frame013_links_0064 record011_frame013_links_0128))
theorem record011_frame013_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 13 :=
  of_group record011 13 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record011_frame013_indices record011_frame013_graph record011_frame013_links
def record011_frame014_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x2c2afebbae2b4ac6aeaaaa7a92649865e96e589565293e4c926328ba2a89e238821d8661684e108320a81a04801fe7f1f87d9f17b9ec7a9e86b9ab6a1a668da167d9c669986097e5f1795dd745c9705b56b5a5645855d56956551515354b5214550d414fd1243105400f93d0f13a8e5388e1370d934cd0328c8314bf2f4ba2e0b52c4ad2a4a52889d2689524c9022c891944511043108411003f0f83d0f023088210801f0781d0701b068110400f0380d0300b02809020060140400c0200400 } : Fields).get c.val)
theorem record011_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 14) (record011.inverseMaps 14) record011_frame014_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record011) (record011.maps 14)
      (record011.inverseMaps 14) record011_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame014_links_0000 (interval_append _ 64 128 153 record011_frame014_links_0064 record011_frame014_links_0128))
theorem record011_frame014_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 14 :=
  of_group record011 14 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record011_frame014_indices record011_frame014_graph record011_frame014_links
def record011_frame015_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0731.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0731.count (({ width := 8, code := 0xd2d1d0cfcecdcccbcac9bcbbbab9b8b7b6b5b4b3acabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a99989796959487868584838281807f7e77767574737271706f6e6d6c6b6a696867666564636261605f5856545351504f4d4c4b4a4846454342413f3e3d3c3b3a393837353332302f2e2c2b2a292827262524232221201f1e1d1c1b1a1918171615100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0731.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record011) (record011.maps 15) (record011.inverseMaps 15) record011_frame015_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0731.localPairCheck (smallEmbedding record011) (record011.maps 15)
      (record011.inverseMaps 15) record011_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame015_links_0000 (interval_append _ 64 128 153 record011_frame015_links_0064 record011_frame015_links_0128))
theorem record011_frame015_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 15 :=
  of_group record011 15 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0731
    Papers.RationalityTen.SharedFrameCatalogue.group0731_facts record011_frame015_indices record011_frame015_graph record011_frame015_links
def record011_frame016_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0183.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0183.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0183.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record011) (record011.maps 16) (record011.inverseMaps 16) record011_frame016_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0183.localPairCheck (smallEmbedding record011) (record011.maps 16)
      (record011.inverseMaps 16) record011_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame016_links_0000 (interval_append _ 64 128 153 record011_frame016_links_0064 record011_frame016_links_0128))
theorem record011_frame016_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 16 :=
  of_group record011 16 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0183
    Papers.RationalityTen.SharedFrameCatalogue.group0183_facts record011_frame016_indices record011_frame016_graph record011_frame016_links
def record011_frame017_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0762.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0762.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0762.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0762.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0762.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0762.localPairCheck (smallEmbedding record011) (record011.maps 17) (record011.inverseMaps 17) record011_frame017_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0762.localPairCheck (smallEmbedding record011) (record011.maps 17)
      (record011.inverseMaps 17) record011_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame017_links_0000 (interval_append _ 64 128 153 record011_frame017_links_0064 record011_frame017_links_0128))
theorem record011_frame017_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 17 :=
  of_group record011 17 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0762
    Papers.RationalityTen.SharedFrameCatalogue.group0762_facts record011_frame017_indices record011_frame017_graph record011_frame017_links
def record011_frame018_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0323.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0323.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0323.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0323.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0323.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0323.localPairCheck (smallEmbedding record011) (record011.maps 18) (record011.inverseMaps 18) record011_frame018_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0323.localPairCheck (smallEmbedding record011) (record011.maps 18)
      (record011.inverseMaps 18) record011_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame018_links_0000 (interval_append _ 64 128 153 record011_frame018_links_0064 record011_frame018_links_0128))
theorem record011_frame018_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 18 :=
  of_group record011 18 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0323
    Papers.RationalityTen.SharedFrameCatalogue.group0323_facts record011_frame018_indices record011_frame018_graph record011_frame018_links
def record011_frame019_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcef66f3331976ca664831f58d2c5361faa294f2a6752b2905456a1850227b93b49844bea5d92de9684b0a5692a694c4a2a4f926e930494a489236914486a4191fe8f6477a3a11c28da37e1b9cdac6c33579a64d0866f32c9910ae85612a794f4a5651828293d09c24d125f12b093448823b919c8aa443219108c8204001f78f7c79e3051790b8059c2bc1548a5850a272131093c47a22b10c88203f01e60ea070c3681a10c886002e01600ab053c29014109d04cc25812508f045c1a205e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record011_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 19) (record011.inverseMaps 19) record011_frame019_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 19)
      (record011.inverseMaps 19) record011_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame019_links_0000 (interval_append _ 64 128 153 record011_frame019_links_0064 record011_frame019_links_0128))
theorem record011_frame019_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 19 :=
  of_group record011 19 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record011_frame019_indices record011_frame019_graph record011_frame019_links
def record011_frame020_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0783.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0783.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0783.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0783.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0783.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0783.localPairCheck (smallEmbedding record011) (record011.maps 20) (record011.inverseMaps 20) record011_frame020_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0783.localPairCheck (smallEmbedding record011) (record011.maps 20)
      (record011.inverseMaps 20) record011_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame020_links_0000 (interval_append _ 64 128 153 record011_frame020_links_0064 record011_frame020_links_0128))
theorem record011_frame020_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 20 :=
  of_group record011 20 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0783
    Papers.RationalityTen.SharedFrameCatalogue.group0783_facts record011_frame020_indices record011_frame020_graph record011_frame020_links
def record011_frame021_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd9f6c535cdab6d43695b4519f8ce4666ab21568aa054629dd4c4a5051da89d42694649924792188fa473a3511828ad44d22210ec864429210906081f4069fecfd27d73e31ed4f4a7932ca1600ad85582a194b8a38507279937c8243fe1f50f6078c3b31d00e346f23661aa0d0866031e1870bf05d62d91638ad454629214089c44be20f10408043f41f30f607943bc1d70e807243841bb0da06b434c19f0cc06443141810bd05cc2d81650b005642a414b0a204f426c12f09404841aa05e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record011_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 21) (record011.inverseMaps 21) record011_frame021_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 21)
      (record011.inverseMaps 21) record011_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame021_links_0000 (interval_append _ 64 128 153 record011_frame021_links_0064 record011_frame021_links_0128))
theorem record011_frame021_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 21 :=
  of_group record011 21 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame021_indices record011_frame021_graph record011_frame021_links
def record011_frame022_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0x1389bcda6b3499cc6612f97486411f8f476391b8cc622f0f86c2e130782c11fefd7dbe9f2f87bbd9eaf478bc1deed763add4e96e36db4d96c35dacd469b4994c86331184c05fae970b65aad166b258ac15eac55aa950a75329548964a249208e4622d108642204fe7d3d9e4ee75389b8d66833190c4612f974b6592b954a64f261246c2e168b0562a148a04e26128783a1c0d86832180b8582a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record011_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 22) (record011.inverseMaps 22) record011_frame022_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (smallEmbedding record011) (record011.maps 22)
      (record011.inverseMaps 22) record011_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame022_links_0000 (interval_append _ 64 128 153 record011_frame022_links_0064 record011_frame022_links_0128))
theorem record011_frame022_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 22 :=
  of_group record011 22 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record011_frame022_indices record011_frame022_graph record011_frame022_links
def record011_frame023_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0335.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0335.count (({ width := 9, code := 0x1168ac52271288c421f0e86c01fefe7ebf1f6fa7cbe1eeef76badd2e772b91c6e270b81bede6eb71b6da6cb61aed66ab51a6d262b1186c260b017ebe5eaf168b2582b958aa54aa14ea652a9146a250a813e9e4ea71369a4ca612e8943a1506813f9f8f87a3c1d4e671379b4d6693318cc05d2d964ae562a148a04e261289045210fc622c158a85228138984a24118783a1c0d86832180b8582a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record011_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0335.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 23) (record011.inverseMaps 23) record011_frame023_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0335.localPairCheck (smallEmbedding record011) (record011.maps 23)
      (record011.inverseMaps 23) record011_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame023_links_0000 (interval_append _ 64 128 153 record011_frame023_links_0064 record011_frame023_links_0128))
theorem record011_frame023_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 23 :=
  of_group record011 23 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0335
    Papers.RationalityTen.SharedFrameCatalogue.group0335_facts record011_frame023_indices record011_frame023_graph record011_frame023_links
def record011_frame024_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6bd6b76b26aa6a169869068767e6785d25ce5c45bb5b25a859d59258657d52b5205135074fd4f34e54d94cc4c34bc4b34aa49f49949248847f47546e46445944f44643b39639238837e37336735d35434a3412ef2e42d72c92bd2b02a429a29028728027726e26225924f24624023923222821d2132071fe1c11bb1b41ae1a619e19618e18617f17d17917216b16515d15514f14714013c13813312e12712311e11a11410d1071000f90f30ed0b305d05c05b05a05905805705605505402602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record011_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 24) (record011.inverseMaps 24) record011_frame024_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 24) (record011.inverseMaps 24) record011_frame024_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 24) (record011.inverseMaps 24) record011_frame024_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 24)
      (record011.inverseMaps 24) record011_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame024_links_0000 (interval_append _ 64 128 153 record011_frame024_links_0064 record011_frame024_links_0128))
theorem record011_frame024_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 24 :=
  of_group record011 24 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record011_frame024_indices record011_frame024_graph record011_frame024_links
def record011_frame025_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x37d6f4de1bab716d6da1b2b606b6cad93b23640c718ab1261ac19802d85a6b3d65ac7580af15bab0554a914fa9b52ca4d462875049f53a2714d498d2fa5945489d1121f42e8450720940c7fceb9d239c728e11bc3726d0d81a9346678cd19532061cc117d2f45ccb81682c6574ac1392684bc971292444808d91722243c8590720a4087e8f81ea3c4758e81c837c6d0d51a4334640c61883005e0ba16e2c8438520a21402784e09a1302584a092098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record011) (record011.maps 25) (record011.inverseMaps 25) record011_frame025_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record011) (record011.maps 25) (record011.inverseMaps 25) record011_frame025_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record011) (record011.maps 25) (record011.inverseMaps 25) record011_frame025_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record011) (record011.maps 25)
      (record011.inverseMaps 25) record011_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame025_links_0000 (interval_append _ 64 128 153 record011_frame025_links_0064 record011_frame025_links_0128))
theorem record011_frame025_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 25 :=
  of_group record011 25 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record011_frame025_indices record011_frame025_graph record011_frame025_links
def record011_frame026_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0938.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0938.count (({ width := 9, code := 0x191c863f1d8dc662b1388c35b2d769b3d96c761afd76b74ba3d12813d9d4de693197cba572a9449e4b2491c86411d8e46a31167ebf1f4f87b3d1e4f0773b1b8d86ab459ccb6431584c05faf176b95c2d96ab4592c55cad55aa54e9a4c259269147235168843a1906813f9f4f67a3c1d8ea72381b8d86a34998c86230178ba5b2c96090391c0dc6c351a0cc64311808c44211007c3c1d0e06c34110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record011_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record011) (record011.maps 26) (record011.inverseMaps 26) record011_frame026_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record011) (record011.maps 26) (record011.inverseMaps 26) record011_frame026_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record011) (record011.maps 26) (record011.inverseMaps 26) record011_frame026_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record011) (record011.maps 26)
      (record011.inverseMaps 26) record011_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame026_links_0000 (interval_append _ 64 128 153 record011_frame026_links_0064 record011_frame026_links_0128))
theorem record011_frame026_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 26 :=
  of_group record011 26 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0938
    Papers.RationalityTen.SharedFrameCatalogue.group0938_facts record011_frame026_indices record011_frame026_graph record011_frame026_links
def record011_frame027_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0782.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0782.count (({ width := 9, code := 0x10c854260f0581c0a03007fbc9e2ef76bb1d2e873b99cae371385bede6db69b0d569b49a2d06733594c96431586c260afd7abc582b958aa5429d4aa451a89409f4f27134994ba51269047a391a8b44a210c8441a00fe7d3e1e8f2773b1d0e672381b8d66934198ca6331184be5d2d964b0562a148a25027938984b2491c8c45219046c2b150a4502713094482311070361a0c8602e160a8502610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record011_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0782.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record011) (record011.maps 27) (record011.inverseMaps 27) record011_frame027_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record011) (record011.maps 27) (record011.inverseMaps 27) record011_frame027_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record011) (record011.maps 27) (record011.inverseMaps 27) record011_frame027_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record011) (record011.maps 27)
      (record011.inverseMaps 27) record011_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame027_links_0000 (interval_append _ 64 128 153 record011_frame027_links_0064 record011_frame027_links_0128))
theorem record011_frame027_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 27 :=
  of_group record011 27 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0782
    Papers.RationalityTen.SharedFrameCatalogue.group0782_facts record011_frame027_indices record011_frame027_graph record011_frame027_links
def record011_frame028_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1048.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1048.count (({ width := 9, code := 0x10d85c2a1107834120702803e9f0f77abd1e6f1783bddae873391c4e06fb79b8db6d365aed569b45a0cf66b3196c96331186c25f2f176b95c2dd6ab459ac558aa5429948a3512813e9e4ea6d32974aa5126914823d1a8a4421d0c83409fcfa7b3d1e4ee763a9d0e470371b0d66a3419ccc643097cbc5d2e16cb4592c15cac552a14c9a391c0dc6c351a0cc64311808842200f8783a1c0d86832110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record011_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record011) (record011.maps 28) (record011.inverseMaps 28) record011_frame028_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record011) (record011.maps 28) (record011.inverseMaps 28) record011_frame028_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record011) (record011.maps 28) (record011.inverseMaps 28) record011_frame028_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record011) (record011.maps 28)
      (record011.inverseMaps 28) record011_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame028_links_0000 (interval_append _ 64 128 153 record011_frame028_links_0064 record011_frame028_links_0128))
theorem record011_frame028_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 28 :=
  of_group record011 28 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1048
    Papers.RationalityTen.SharedFrameCatalogue.group1048_facts record011_frame028_indices record011_frame028_graph record011_frame028_links
def record011_frame029_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0935.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0935.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0935.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0935.localPairCheck (smallEmbedding record011) (record011.maps 29) (record011.inverseMaps 29) record011_frame029_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0935.localPairCheck (smallEmbedding record011) (record011.maps 29) (record011.inverseMaps 29) record011_frame029_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0935.localPairCheck (smallEmbedding record011) (record011.maps 29) (record011.inverseMaps 29) record011_frame029_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0935.localPairCheck (smallEmbedding record011) (record011.maps 29)
      (record011.inverseMaps 29) record011_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame029_links_0000 (interval_append _ 64 128 153 record011_frame029_links_0064 record011_frame029_links_0128))
theorem record011_frame029_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 29 :=
  of_group record011 29 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0935
    Papers.RationalityTen.SharedFrameCatalogue.group0935_facts record011_frame029_indices record011_frame029_graph record011_frame029_links
def record011_frame030_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3776e4db5b3b606b4d4da634667eb696aad0594b0d5eab655eaa55127b4f09d53926f4d89a5332634c09752d2574a89452724b4909152123d4748dd1a2313a873ce51c437a6dcd81a9346670ba9722de5b0b49662c6580ae95a2ae550a894e296520a294227e4f09b9342624b89590c212418819001fa3e87b8f41e23b8758e81ca3886f8dc1b2358698ce196320628c21823005f8be17a2f05d8ba1722e05685c0b61682c8580ae1582a8540a6098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 30) (record011.inverseMaps 30) record011_frame030_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 30) (record011.inverseMaps 30) record011_frame030_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 30) (record011.inverseMaps 30) record011_frame030_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 30)
      (record011.inverseMaps 30) record011_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame030_links_0000 (interval_append _ 64 128 153 record011_frame030_links_0064 record011_frame030_links_0128))
theorem record011_frame030_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 30 :=
  of_group record011 30 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record011_frame030_indices record011_frame030_graph record011_frame030_links
def record011_frame031_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xcb8658b2a9948c9d64b323d910c8163d2b6d5aaace563ab01572ab2555aa9153a9aa4cc26192ec9644a9a50125a91b48523dd1ca8d3461a2c514088d43d21a10ae84b42220f506c82f33e19d4cde6683309968ca664c32298fcaf256c2af9544a865352931460a144fc276137c9a44c425b12a093248b23e91bc8ca46022d91588a236d1af8d3c67e33018f8c385fc2ee16e8b3057c2ae14f0a3c4fc26d12e8934478231115088c43821510307c83c01cc0db868831c17c0b5055c1a405e02e81700b605a02c81600ae05602a809804a024011808804202000f807803a011008003c01c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record011_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record011) (record011.maps 31) (record011.inverseMaps 31) record011_frame031_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record011) (record011.maps 31) (record011.inverseMaps 31) record011_frame031_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record011) (record011.maps 31) (record011.inverseMaps 31) record011_frame031_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record011) (record011.maps 31)
      (record011.inverseMaps 31) record011_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame031_links_0000 (interval_append _ 64 128 153 record011_frame031_links_0064 record011_frame031_links_0128))
theorem record011_frame031_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 31 :=
  of_group record011 31 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record011_frame031_indices record011_frame031_graph record011_frame031_links
def record011_frame032_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x68467e67a67767367266c66565f65b5d55ce5cb5c65c35c05ba5b45ad5a854f54653b53152c52951f5115095004f74ed4e84e34d84d14c74b94b24a94a149a49348f48b3c53c03bb3b73b23af3a93a339d39933933132832131b31830f3022fd2f62ea2e22dc2d82cf2c92c02b32ad2a72a029b29629329022c22521e21520d2091fe1ef1e81e01d51cc1c41c01b91b21a719819018a18217b17417016c16215914f14713d13712b12011610b0ae05c05b05a05905805705605505405302602502402302202102001f01e01d01101000f00e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record011_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record011) (record011.maps 32) (record011.inverseMaps 32) record011_frame032_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record011) (record011.maps 32) (record011.inverseMaps 32) record011_frame032_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record011) (record011.maps 32) (record011.inverseMaps 32) record011_frame032_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record011) (record011.maps 32)
      (record011.inverseMaps 32) record011_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame032_links_0000 (interval_append _ 64 128 153 record011_frame032_links_0064 record011_frame032_links_0128))
theorem record011_frame032_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 32 :=
  of_group record011 32 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record011_frame032_indices record011_frame032_graph record011_frame032_links
def record011_frame033_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0931.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0931.count (({ width := 9, code := 0x12a94ca24f2692c92472290c4e25118843e1d0d8642e14ff7ebedf0f679bc5deec753a1cce470b7db8da6c355a6cf66b2d92c75d2e16eb65aad166b258ac152a75329146a15027d3a9c4da6530964aa4d249147a39188a44a210e803e9f0f4793b9d8ea73391c4dc6d359a8d06733190c6613017cbc5d2d160ae5329138984b23914622d160ac54291409c4c25120783a1c0d86832180b8582a10078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record011_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0931.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record011) (record011.maps 33) (record011.inverseMaps 33) record011_frame033_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record011) (record011.maps 33) (record011.inverseMaps 33) record011_frame033_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame033_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record011) (record011.maps 33) (record011.inverseMaps 33) record011_frame033_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record011) (record011.maps 33)
      (record011.inverseMaps 33) record011_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame033_links_0000 (interval_append _ 64 128 153 record011_frame033_links_0064 record011_frame033_links_0128))
theorem record011_frame033_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 33 :=
  of_group record011 33 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0931
    Papers.RationalityTen.SharedFrameCatalogue.group0931_facts record011_frame033_indices record011_frame033_graph record011_frame033_links
def record011_frame034_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0954.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0954.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0954.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record011) (record011.maps 34) (record011.inverseMaps 34) record011_frame034_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record011) (record011.maps 34) (record011.inverseMaps 34) record011_frame034_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame034_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record011) (record011.maps 34) (record011.inverseMaps 34) record011_frame034_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0954.localPairCheck (smallEmbedding record011) (record011.maps 34)
      (record011.inverseMaps 34) record011_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame034_links_0000 (interval_append _ 64 128 153 record011_frame034_links_0064 record011_frame034_links_0128))
theorem record011_frame034_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 34 :=
  of_group record011 34 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0954
    Papers.RationalityTen.SharedFrameCatalogue.group0954_facts record011_frame034_indices record011_frame034_graph record011_frame034_links
def record011_frame035_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0729.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0729.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0729.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0729.localPairCheck (smallEmbedding record011) (record011.maps 35) (record011.inverseMaps 35) record011_frame035_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0729.localPairCheck (smallEmbedding record011) (record011.maps 35) (record011.inverseMaps 35) record011_frame035_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame035_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0729.localPairCheck (smallEmbedding record011) (record011.maps 35) (record011.inverseMaps 35) record011_frame035_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0729.localPairCheck (smallEmbedding record011) (record011.maps 35)
      (record011.inverseMaps 35) record011_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame035_links_0000 (interval_append _ 64 128 153 record011_frame035_links_0064 record011_frame035_links_0128))
theorem record011_frame035_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 35 :=
  of_group record011 35 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0729
    Papers.RationalityTen.SharedFrameCatalogue.group0729_facts record011_frame035_indices record011_frame035_graph record011_frame035_links
def record011_frame036_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0182.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0182.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0182.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0182.localPairCheck (smallEmbedding record011) (record011.maps 36) (record011.inverseMaps 36) record011_frame036_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0182.localPairCheck (smallEmbedding record011) (record011.maps 36) (record011.inverseMaps 36) record011_frame036_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame036_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0182.localPairCheck (smallEmbedding record011) (record011.maps 36) (record011.inverseMaps 36) record011_frame036_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0182.localPairCheck (smallEmbedding record011) (record011.maps 36)
      (record011.inverseMaps 36) record011_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame036_links_0000 (interval_append _ 64 128 153 record011_frame036_links_0064 record011_frame036_links_0128))
theorem record011_frame036_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 36 :=
  of_group record011 36 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0182
    Papers.RationalityTen.SharedFrameCatalogue.group0182_facts record011_frame036_indices record011_frame036_graph record011_frame036_links
def record011_frame037_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0914.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0914.count (({ width := 8, code := 0xabaaa9a8a7a6a5a4a3a2a09f9e9d9c9b9a9998979594939291908f8e8d8c8a8988878685848382817f7d7c7b7a7977767574737271706f6e6c6b6a6968676665646361605f5e5d5c5b5a59585655545352504f4e4d4c4b4a4948474544434241403f3e3d3b3a3938373534333231302f2e2d2c27262524232221201f1e1d1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame037_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0914.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame037_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record011) (record011.maps 37) (record011.inverseMaps 37) record011_frame037_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame037_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record011) (record011.maps 37) (record011.inverseMaps 37) record011_frame037_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame037_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record011) (record011.maps 37) (record011.inverseMaps 37) record011_frame037_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame037_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0914.localPairCheck (smallEmbedding record011) (record011.maps 37)
      (record011.inverseMaps 37) record011_frame037_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame037_links_0000 (interval_append _ 64 128 153 record011_frame037_links_0064 record011_frame037_links_0128))
theorem record011_frame037_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 37 :=
  of_group record011 37 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0914
    Papers.RationalityTen.SharedFrameCatalogue.group0914_facts record011_frame037_indices record011_frame037_graph record011_frame037_links
def record011_frame038_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0694.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0694.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame038_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0694.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame038_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0694.localPairCheck (smallEmbedding record011) (record011.maps 38) (record011.inverseMaps 38) record011_frame038_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame038_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0694.localPairCheck (smallEmbedding record011) (record011.maps 38) (record011.inverseMaps 38) record011_frame038_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame038_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0694.localPairCheck (smallEmbedding record011) (record011.maps 38) (record011.inverseMaps 38) record011_frame038_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame038_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0694.localPairCheck (smallEmbedding record011) (record011.maps 38)
      (record011.inverseMaps 38) record011_frame038_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame038_links_0000 (interval_append _ 64 128 153 record011_frame038_links_0064 record011_frame038_links_0128))
theorem record011_frame038_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 38 :=
  of_group record011 38 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0694
    Papers.RationalityTen.SharedFrameCatalogue.group0694_facts record011_frame038_indices record011_frame038_graph record011_frame038_links
def record011_frame039_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0084.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0084.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame039_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0084.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame039_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0084.localPairCheck (smallEmbedding record011) (record011.maps 39) (record011.inverseMaps 39) record011_frame039_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame039_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0084.localPairCheck (smallEmbedding record011) (record011.maps 39) (record011.inverseMaps 39) record011_frame039_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame039_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0084.localPairCheck (smallEmbedding record011) (record011.maps 39) (record011.inverseMaps 39) record011_frame039_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame039_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0084.localPairCheck (smallEmbedding record011) (record011.maps 39)
      (record011.inverseMaps 39) record011_frame039_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame039_links_0000 (interval_append _ 64 128 153 record011_frame039_links_0064 record011_frame039_links_0128))
theorem record011_frame039_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 39 :=
  of_group record011 39 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0084
    Papers.RationalityTen.SharedFrameCatalogue.group0084_facts record011_frame039_indices record011_frame039_graph record011_frame039_links
def record011_frame040_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x577ae75b6b4564ac1566a954da8f342664c69832f65ccb295729a504638b9152274488850ee1a42c84b07a0bc0f81300dfebf67def9df03db7aef4de7bcb6bcd65aa34f694d159fb39664cad6c2d0592b0d5f2bb566aa55129b520a254127a4ea9c133a5c4a6925202394688bd149d639e720e01bb36c6b4d119931e614be9762e05acb41602ac53ca41402724d0979292464708a90f2124087e0f51dc39c530550a814c290510a013c2704d098098128240460881082003e0780e81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame040_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame040_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record011) (record011.maps 40) (record011.inverseMaps 40) record011_frame040_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame040_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record011) (record011.maps 40) (record011.inverseMaps 40) record011_frame040_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame040_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record011) (record011.maps 40) (record011.inverseMaps 40) record011_frame040_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame040_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record011) (record011.maps 40)
      (record011.inverseMaps 40) record011_frame040_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame040_links_0000 (interval_append _ 64 128 153 record011_frame040_links_0064 record011_frame040_links_0128))
theorem record011_frame040_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 40 :=
  of_group record011 40 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record011_frame040_indices record011_frame040_graph record011_frame040_links
def record011_frame041_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x4d89a933a63cc297f2ea59cad94b1222243f8770d617c2a84706e0abe37b8f51e73cb78cf05dcbb3756e91cf39b72ae35c3b826f4dd1b6b666c4d71ab3525dcba5712dc5aab4565ac557eae93e27a4ec9bd35a684c09612aa4e48c9051da3345a8a10f21541e81cff1f83e67b8f41a9346674cb991316604bc1712d0580ad9572a8540a61442784d89992c24c47c8d916220424820fd1f03c8768e91c63745305a0b21602b8560aa150298520a2094120230440841001f03c0740e01102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame041_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame041_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record011) (record011.maps 41) (record011.inverseMaps 41) record011_frame041_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame041_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record011) (record011.maps 41) (record011.inverseMaps 41) record011_frame041_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame041_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record011) (record011.maps 41) (record011.inverseMaps 41) record011_frame041_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame041_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record011) (record011.maps 41)
      (record011.inverseMaps 41) record011_frame041_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame041_links_0000 (interval_append _ 64 128 153 record011_frame041_links_0064 record011_frame041_links_0128))
theorem record011_frame041_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 41 :=
  of_group record011 41 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record011_frame041_indices record011_frame041_graph record011_frame041_links
def record011_frame042_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x41582302603403802fe5f9bef7d0e91d039d732e5dc8388708df5bbb556a0d2da3b44680ced9bb3265ac9d91b1f638c618930e612c117f2f85e6bb5732e34e09a931a5d4ae949262474848f5052074027f0fc1f73e07a4f29df3b274ce71c9388704dc9b335a69cd099c32e648c795d2ac548a814a28a4fc9b93125649c9111e2384688a10e2104007d0f51e23a8728e31be3686a8d119831c628c217e2f04a8560aa150298520a21402784e09a090118220420800f81e03a0700d81102003c0700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record011_frame042_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame042_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record011) (record011.maps 42) (record011.inverseMaps 42) record011_frame042_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame042_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record011) (record011.maps 42) (record011.inverseMaps 42) record011_frame042_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame042_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record011) (record011.maps 42) (record011.inverseMaps 42) record011_frame042_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame042_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record011) (record011.maps 42)
      (record011.inverseMaps 42) record011_frame042_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame042_links_0000 (interval_append _ 64 128 153 record011_frame042_links_0064 record011_frame042_links_0128))
theorem record011_frame042_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 42 :=
  of_group record011 42 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record011_frame042_indices record011_frame042_graph record011_frame042_links
def record011_frame043_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0693.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0693.count (({ width := 8, code := 0x9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record011_frame043_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0693.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame043_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0693.localPairCheck (smallEmbedding record011) (record011.maps 43) (record011.inverseMaps 43) record011_frame043_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame043_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0693.localPairCheck (smallEmbedding record011) (record011.maps 43) (record011.inverseMaps 43) record011_frame043_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame043_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0693.localPairCheck (smallEmbedding record011) (record011.maps 43) (record011.inverseMaps 43) record011_frame043_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame043_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0693.localPairCheck (smallEmbedding record011) (record011.maps 43)
      (record011.inverseMaps 43) record011_frame043_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame043_links_0000 (interval_append _ 64 128 153 record011_frame043_links_0064 record011_frame043_links_0128))
theorem record011_frame043_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 43 :=
  of_group record011 43 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0693
    Papers.RationalityTen.SharedFrameCatalogue.group0693_facts record011_frame043_indices record011_frame043_graph record011_frame043_links
def record011_frame044_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1097.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1097.count (({ width := 9, code := 0x1168ac52271288c3e1d0d85c12070280c01fefd7e3edf2ee76badd2e772b91c4e06fb79badb6cb5daad4693419ece66b3196ca62b1186c260b017cbd5e2e95eae562a950a652a8d42a04fa79389a4c2592a9348a411e8e46a311682409fcfa7b3c9e0ec74399c8e26f369acd26833190c66230980be5e2e970b65a2c960ae562a9509e3c1d8e872381b8d86a34198904622108803e1e0e87036110803c1c0d0602c1409040180a04018080200 } : Fields).get c.val)
theorem record011_frame044_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame044_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record011) (record011.maps 44) (record011.inverseMaps 44) record011_frame044_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame044_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record011) (record011.maps 44) (record011.inverseMaps 44) record011_frame044_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame044_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record011) (record011.maps 44) (record011.inverseMaps 44) record011_frame044_indices (Fin.ofNat record011.n i)) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem record011_frame044_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1097.localPairCheck (smallEmbedding record011) (record011.maps 44)
      (record011.inverseMaps 44) record011_frame044_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 153 record011_frame044_links_0000 (interval_append _ 64 128 153 record011_frame044_links_0064 record011_frame044_links_0128))
theorem record011_frame044_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 44 :=
  of_group record011 44 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1097
    Papers.RationalityTen.SharedFrameCatalogue.group1097_facts record011_frame044_indices record011_frame044_graph record011_frame044_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (Fin.cases (record011_frame011_supported hcells) (Fin.cases (record011_frame012_supported hcells) (Fin.cases (record011_frame013_supported hcells) (Fin.cases (record011_frame014_supported hcells) (Fin.cases (record011_frame015_supported hcells) (Fin.cases (record011_frame016_supported hcells) (Fin.cases (record011_frame017_supported hcells) (Fin.cases (record011_frame018_supported hcells) (Fin.cases (record011_frame019_supported hcells) (Fin.cases (record011_frame020_supported hcells) (Fin.cases (record011_frame021_supported hcells) (Fin.cases (record011_frame022_supported hcells) (Fin.cases (record011_frame023_supported hcells) (Fin.cases (record011_frame024_supported hcells) (Fin.cases (record011_frame025_supported hcells) (Fin.cases (record011_frame026_supported hcells) (Fin.cases (record011_frame027_supported hcells) (Fin.cases (record011_frame028_supported hcells) (Fin.cases (record011_frame029_supported hcells) (Fin.cases (record011_frame030_supported hcells) (Fin.cases (record011_frame031_supported hcells) (Fin.cases (record011_frame032_supported hcells) (Fin.cases (record011_frame033_supported hcells) (Fin.cases (record011_frame034_supported hcells) (Fin.cases (record011_frame035_supported hcells) (Fin.cases (record011_frame036_supported hcells) (Fin.cases (record011_frame037_supported hcells) (Fin.cases (record011_frame038_supported hcells) (Fin.cases (record011_frame039_supported hcells) (Fin.cases (record011_frame040_supported hcells) (Fin.cases (record011_frame041_supported hcells) (Fin.cases (record011_frame042_supported hcells) (Fin.cases (record011_frame043_supported hcells) (Fin.cases (record011_frame044_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record011_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059
