module
prelude
public import GraphInputsRow29Part00291Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups009Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00291
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
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x13f653ca093123e46c879010c214c2483f05a09c0c77ced5d6ba873ede9b936b6c8d6daa34e690d11a032b602b816dad75a6b3d65ac357caf15b2764d89852924e4888d91621c41c81cfd9f33e07a4f19dc32a624c01782d657ca814627c4d8959212364508810a2063906e8d61a232c640c31562a8490820f81b0330530a41442704d0980fc1f03706c0a4128230440841001e03a0700a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x349583ac035f72f697a4bb45cf29fd4d0a6052c28c9448a11496244d1fc8ea46a21c50b284641a207d01c7f63ee1f18f5e75b3789a9cd3268833e19accc264e31e18c8c425972bd9594a8453629414209d44d22571288928482239917c8a04401c60db06c434f1948c5c5c62c215c0a9450226f12e891c46822210706e43501970c305d82c6150087040019209e04a01e80e005c02d81680ae05602a810c08403901c00a804c024011808804201f00f0074028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x70267e67767266a66665f65b5cb5c35c05bb5b25ad5a852951a50f5095004d14c24b74b24a94a349b49348f48b4463f73c53c03bb3b73b23af3a73a139d3993313213183002fd2f62e22d82c92b12ad2a72a029c29629329021e20d2091fb1e81e01c41b91b21a419018a18317b17417016c13712811f11610b0fe0f60d40cc0ae09208c07606e05a05905805505405304204103903802a02602402302202101f01e01d01401000f00e00d00b00a009008004003002001000 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0xe71ba36b6c6d65ac353692c798c31161ac0d7f2f9590b11602bd56ea5d48a8b510a093ea774dc9a131a4f4668810ea17424835042003f47e4f91c73766d0d49a633e664c79842f05dcb916a2d2588af15a25c4989091c2224307e8f51e23a8718de1b4348670ca18e2b8558a814e2904f09a11a228400730dc1943005009e1382584a09210c210390700a8130240460881081f03c0740a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x117a08c06802fd9fabef7d0e75cbb90714e05beb77680ce59ab3265ac4986307608bf97d2f55dab9971ac15229c1352634ba95d292494889091ea073f87dcf39e53be74ce49c13626b4d39a133c65cc918f2a4528a293d2624ac8f11a228430800fa1ee3c4750e51c631c620c117e2f05c0b314a28c4a8790ea19c310540a61482784e09a0f41e0350680a0120220420800f81d03806c0a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
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
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x12b653ca090f1121e43185308de53bf76eec5d0b696c2d61a934b688cf998b245acb315f2b255c9692824a4888e9031fd3ea7bcf41e03b6738dd9a233e668ca98f31460cbe96c2c0550a193d26c49c8b1021ea3c0738d91a4328590aa1481f03d8670c6188308580a814c2904e09a130258370660c41802804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2fb57c6bca5a92a214e2a5f525a8e52b2936496246d1fe87142e212106881f4031fccf6275e34b19e4cc06513219628adc5652ad150c9a44c1258128892848123811088023ad1cd8e306f636c1b10d406762f41698ae052628113789204201e00e186e43541860bb0594242110080823811a07103681ac0d406102e81700b605702b01540a803901a80cc064029012809004601f00f007403801500a004402000f0070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6c66b666b5e85d85cd5c15b953d52a52551e50e4c94bd4b14a749a48c4844644313ad39f39338737f3012f22eb2e42d428f28327726a25f25224a22a2091e11d91d01c81bf1b91b41ad19017f17016515f15714913212211611010c1010f90f20da0d40d008a08906f06b06906805f05b05a05905505405305203903503303202902502402301f01e01d01c01501401101000f00e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x101a013ff7cae99cbb9070ce05a033465aca18e2f85e4bad73ae25b4b5163aa64ca95d27a464847f8f91ec3d0774dc9b335a6a4d219d32e62cba95f2b0544a51412744cc9712423644c851062023d0710d61a232c640bd1742cc4d0951221b8368600ba16c2d0540a21402784b094124240340620bc1702804a0901181f03c0740e0150280440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc8d63e28a142e9ae4bea5bd2c2958498248923691348323fd1ee8f146e1a58d065e32b094f4a3050324d11dc8ce454219108c8224021e88dd05e42ce1548a504562080fc07943861b40d1064c2c41560a7852028213a099847822e10a07b03bc12608e04681c00d606a03101840bc05c02d81600ae05602a815007003301900a8052026012008c04001f00f007403801500a004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd28689a97d49e9b649924311ce8d2432210906081e3fd9fa4fb07c83ca94aca364821ff0f6076639e1980c385f82ea1638ad454829413088e44101fa0f6078c3761ad0d3067832218a0c105f02ce1600ac854829614409e84a024211307f03dc12608e04681c00d606a03101840bc05c02d81600ae05602a815007003301900a8052026012008c04001f00f007403801500a004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x327644a714ba714b89592824b4768d51922e4528991122042e6a0d197d2d0588ae15728e5049f13a26a4c89712c2464507f8f91e63b86f0d81aa344660c918a30c5d0b716c2d45a0b31642bc570ac1522a0438821021a8328640b816c2c0560aa1482885009e1381c0330640a81482604808c1001f03c0740e0150280440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3576a4ae95aa8d4f09c9362674ae9452724a48a9091f23c4666d0d79872e45b0b31612a252ca414427e4f09c13625a478849031fa3e0740e21be36c6b0d319e334620c11802fc5f0bd1782e45c0b61662c84788a1121b8348680c017c2e05a0b21582a8540a61481c0330640a81482604808c1001f03c0740e0150280440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x25e96e1b861f8795df765d4715bf6f1b86cdb06b1aa685735c1504f5374c52c475174511042d08411023e4eb360d2330c72e0b22bcab298a327c9d250912408f2388d230892208620c821c06c1ac5e16859144501344b1284711845110430dc330c82a0a426090230801f0781d070150501103c0e02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xbed5f0a97d49e9d54b5a52125891744f21ed0e285e41a207d0107f43d89980caa5ea2cb95ecaca55627c936c9a44c32511250906471221100473637b1b10d405c62c215c0a9c50226f12d09244201fd0f707803a21c30dc86182ec151090844412608e04681c00d606a03101840bc05c02d81600ae05602a815007003301900a8052026012008c04001f00f007403801500a004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6ce6c45cd5c557d54553252551a4df4ce4c94bf4a749a48e48546439338b3433092fa2eb2e02a229428f28526a25f25424b22a2091d91c81b91b418817717016b15f15714e14a13212d12812211c1161101010f90ee0da0d508f08a08906e06906806005f05c05a05905605505405305203803303202a02902602402302001f01e01d01c01501401100f00e00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record002_frame007_links_0000 record002_frame007_links_0064)
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabfa55a46a39a28a1497f9038f18e48d68c48937f77df7ce7bf7a879c7937837727637537367227167036f06de6c36b069d61959d58c57f57056253e4bd4ab49d4904804764704634554474394204104073f83e93db3c23b33a33792e72d82cc2be2ac2a029628627526725a22821a2091fa1c21ba1ae1a019118315614613712b0f10e60d90cc0be0b206f06e06906806706005f05a05905803903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame001_links_0000 (interval_append _ 64 128 129 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc7c5f82fa57a6bba5d22b8d4bea4c51b288541c9d549624612008ea46a23151668a144821f90e485a42220dd04480c3fb9f64f867ac3789980ca46403179878bd45652ab9510a6c52828e142c9f84ed26f134c97e4ac252925c90e47422e113487a4011b10d4467832918b8c185e82e31698b08570281137896c4921fd0f707803a21c30dc86182ec1660a8843c1fe0f2072835818e07103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame002_links_0000 (interval_append _ 64 128 129 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x11086c2a110682405fefe7ebf1f6f97bbd5e6f177bb5d4e772385bcda6b34da2cf66b298cc35faf174b85b2d166b258ac15eae562a54ca35027534974a249208e462250c8441a0902803f9f4f6793b9d4e66d359a4ce5f2e96cb2572a9449e4d25914843f1e0dc662d160ac54291409c4c251207c3c1d0e06c34190c05c2c110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame003_links_0000 (interval_append _ 64 128 129 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0153.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0153.count (({ width := 9, code := 0x10c84c1a0902803f5f6fa7cbe1eef579bc5deed75ba5cce370375b4d66933d9acb64b1984c05e2e56eb559ac560af572b558ab54a9946a04ea692e9448a3d1a8b44a19088240a00fe7e3e9ecf2773a9cce26b3499cca5e2e168b0562a1409c4c25114843f1e0dc662d160ac54291409c4c251207c3c1d0e06c34190c05c2c110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame004_links_0000 (interval_append _ 64 128 129 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0153
    Papers.RationalityTen.SharedFrameCatalogue.group0153_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd5768534119facf56772df1560a9c54429e14cca104a224c123890c47d23bd1d08e146d234d1988c345e22dd1608a9451226512488b39399c8cbc64b31c98a0ba451d28493d89c84d326413049744b3256929893a496248922890647d23a91bc8d240318c8c0c5de2da1638ae455229914509e84d623c116887441c1d60e306d834e1970c4056429413a09583dc1e00e9071036c1a807103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame005_links_0000 (interval_append _ 64 128 129 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ad77276e7677607596d467166465364b63f6195b65a959859058557c57556e56756055b55354c54754053953252852151b47b40f4023f13e63db3ae34233532431930e3073002f92f22eb2e62de2d72d22cb2c52be2b52af2aa27d2041f41e91de1d41cb1c31bc1b51ae1a818f18617c17014b14313c13512e12810d1070fc0f00ce0c90c30c00bd0b707107006b06a06906206105c05b05a03903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame006_links_0000 (interval_append _ 64 128 129 record003_frame006_links_0064 record003_frame006_links_0128))
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
def record003_frame007_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x41f81100e003fe7f0f25c83876fede9b9b6665ac998eb17620c3184304602bf97d2f15d4ba171adc5acb3d652c650e93d23a404768d1121ec3cc778ec1d139a724e29c237e6ecd91ac354694cf999324638c51752744d09792c2524989211e236458899062023f07a8de1b4358698d11962f45d0b415c2504808c110218410600be16c2d0590aa1502804f09c0d01982f05c0b41482804808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record003_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 7) (record003.inverseMaps 7) record003_frame007_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 7)
      (record003.inverseMaps 7) record003_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame007_links_0000 (interval_append _ 64 128 129 record003_frame007_links_0064 record003_frame007_links_0128))
theorem record003_frame007_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 7 :=
  of_group record003 7 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record003_frame007_indices record003_frame007_graph record003_frame007_links
def record003_frame008_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x155a9d46a14fa75167f3e9ecee7335984ba592b954a64f2490c7a37178a44e25118843615077f3e1eef67a3c9dce973b95c8e371381bada6bb51a0cd6632d94c96330d80ae4da6530974b251228e45a210c8341200fc74391bcd86933174b65a2c9449c4b24118863c1d8e872381b0d46833190a04e261289044211007c3c110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record003_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record003) (record003.maps 8) (record003.inverseMaps 8) record003_frame008_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record003) (record003.maps 8)
      (record003.inverseMaps 8) record003_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame008_links_0000 (interval_append _ 64 128 129 record003_frame008_links_0064 record003_frame008_links_0128))
theorem record003_frame008_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 8 :=
  of_group record003 8 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record003_frame008_indices record003_frame008_graph record003_frame008_links
def record003_frame009_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0149.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0149.count (({ width := 9, code := 0x13b9ccde6d359a4b24d259248a411c8bc56271288c421d0b8441604fe7dbe9f2f87bbd1e2ee73381bede6e369acd167b3598cb653218ac25faf170b55a2cd64b1572ad509e4622d14894421908813f1ecf2763a9cce26732988be5c2c9449e4e26914843f1e0e86e351a0cc6431180bc5c2d16094482311084401f0f07438110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record003_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record003) (record003.maps 9) (record003.inverseMaps 9) record003_frame009_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (smallEmbedding record003) (record003.maps 9)
      (record003.inverseMaps 9) record003_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame009_links_0000 (interval_append _ 64 128 129 record003_frame009_links_0064 record003_frame009_links_0128))
theorem record003_frame009_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 9 :=
  of_group record003 9 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0149
    Papers.RationalityTen.SharedFrameCatalogue.group0149_facts record003_frame009_indices record003_frame009_graph record003_frame009_links
def record003_frame010_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0127.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0127.count (({ width := 9, code := 0x1a3d067f3d9dce61ef77abc5daeb72b3592c560afd7abb5bacd5eab53a8d429d4da65268f459849247218fc7a370f86c2e130883c1a0902803f9f8fa7cbddecf5793c1dcd457aad54a853291409d4d25d2a8d45a250e7e3e1e4ec73381a0c86330954a44f2612c923e1e8ec74391b8d86833190a04e251208c42200f07438130903c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record003_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record003) (record003.maps 10) (record003.inverseMaps 10) record003_frame010_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (smallEmbedding record003) (record003.maps 10)
      (record003.inverseMaps 10) record003_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame010_links_0000 (interval_append _ 64 128 129 record003_frame010_links_0064 record003_frame010_links_0128))
theorem record003_frame010_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 10 :=
  of_group record003 10 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0127
    Papers.RationalityTen.SharedFrameCatalogue.group0127_facts record003_frame010_indices record003_frame010_graph record003_frame010_links
def record003_frame011_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe30698b471a0acea669acfd4bea4c51ba8914209b6473a34d1808ad44d222d0f286742aa11506681a4041ff8fd87dc3e59ec8f4479030594aca3050327813709043b31cf8e306f23661ab8d146663211888bfc5cc2d41650ae055029713f09b84b82390f607903ba1d70e807243841bb0da06b434c1910c5060c2f81600ac854829614409e84a024211a08983d41dc0e707003641a607103801ac0d406903101840b805b02d00e407003301900c4054029012008c04401500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record003_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 11) (record003.inverseMaps 11) record003_frame011_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 11)
      (record003.inverseMaps 11) record003_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame011_links_0000 (interval_append _ 64 128 129 record003_frame011_links_0064 record003_frame011_links_0128))
theorem record003_frame011_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 11 :=
  of_group record003 11 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame011_indices record003_frame011_graph record003_frame011_links
def record003_frame012_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6d167166365664963a5d057656b55d55754c52b4cb4be4b04aa49e49649248647b46f46845444543f43342941c40b4023f639733d32f32731e3132f229228427927126525d25624d24023822f21920c2061fa1ed1e41d21c91bd1ac17116b16516115d15715414f14914313d12d12912511f10c10a1051000fb0f60e50e00da0d40be0b80b30af0aa0a706a06906406306205b05a05505405303903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record003_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 12) (record003.inverseMaps 12) record003_frame012_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record003) (record003.maps 12)
      (record003.inverseMaps 12) record003_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame012_links_0000 (interval_append _ 64 128 129 record003_frame012_links_0064 record003_frame012_links_0128))
theorem record003_frame012_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 12 :=
  of_group record003 12 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record003_frame012_indices record003_frame012_graph record003_frame012_links
def record003_frame013_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x71a6d16ca6bc6ad6a16255cd5c25b65ac59f57d52551b50f5054f84f14ea4e24db4d14ca4bb4ad4aa49d49248847646a45f3eb39338837c36f3653432eb2e12d52c82bf2b72af2a529f29729028127326d26225824e23922f2252091b91b51ae1a81a019819018817f17717015f15714f14a12d12812211c1161101010f90f30ee0d30ce0c70bf0b80b206f06e06906806706005f05a05905803903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record003_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 13) (record003.inverseMaps 13) record003_frame013_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 13)
      (record003.inverseMaps 13) record003_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame013_links_0000 (interval_append _ 64 128 129 record003_frame013_links_0064 record003_frame013_links_0128))
theorem record003_frame013_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 13 :=
  of_group record003 13 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record003_frame013_indices record003_frame013_graph record003_frame013_links
def record003_frame014_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0258.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0258.count (({ width := 8, code := 0xa09f9e9d9c9b9a9897969492918f8e8d8b898887868584838281807f7e7d7b7977757472706f6e6c6b6967666564636261605f5d5b5a595857565553514f4e4d4c4b4a49484746454241403f3b3a39383736333231302c2b2a29272524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0258.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record003) (record003.maps 14) (record003.inverseMaps 14) record003_frame014_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0258.localPairCheck (smallEmbedding record003) (record003.maps 14)
      (record003.inverseMaps 14) record003_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame014_links_0000 (interval_append _ 64 128 129 record003_frame014_links_0064 record003_frame014_links_0128))
theorem record003_frame014_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 14 :=
  of_group record003 14 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0258
    Papers.RationalityTen.SharedFrameCatalogue.group0258_facts record003_frame014_indices record003_frame014_graph record003_frame014_links
def record003_frame015_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0152.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0152.count (({ width := 8, code := 0xa09f9e9d9c9b9a9897969492918f8e8d8b898887868584838281807f7e7d7b7977757472706f6e6c6b6967666564636261605f5d5b5a595857565553514f4e4d4c4b4a49484746454241403f3b3a39383736333231302c2b2a29272524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0152.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record003) (record003.maps 15) (record003.inverseMaps 15) record003_frame015_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0152.localPairCheck (smallEmbedding record003) (record003.maps 15)
      (record003.inverseMaps 15) record003_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame015_links_0000 (interval_append _ 64 128 129 record003_frame015_links_0064 record003_frame015_links_0128))
theorem record003_frame015_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 15 :=
  of_group record003 15 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0152
    Papers.RationalityTen.SharedFrameCatalogue.group0152_facts record003_frame015_indices record003_frame015_graph record003_frame015_links
def record003_frame016_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0230.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0230.count (({ width := 8, code := 0x807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0230.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0230.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0230.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0230.localPairCheck (smallEmbedding record003) (record003.maps 16) (record003.inverseMaps 16) record003_frame016_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0230.localPairCheck (smallEmbedding record003) (record003.maps 16)
      (record003.inverseMaps 16) record003_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame016_links_0000 (interval_append _ 64 128 129 record003_frame016_links_0064 record003_frame016_links_0128))
theorem record003_frame016_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 16 :=
  of_group record003 16 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0230
    Papers.RationalityTen.SharedFrameCatalogue.group0230_facts record003_frame016_indices record003_frame016_graph record003_frame016_links
def record003_frame017_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0129.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0129.count (({ width := 8, code := 0x807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record003_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0129.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0129.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0129.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0129.localPairCheck (smallEmbedding record003) (record003.maps 17) (record003.inverseMaps 17) record003_frame017_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0129.localPairCheck (smallEmbedding record003) (record003.maps 17)
      (record003.inverseMaps 17) record003_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame017_links_0000 (interval_append _ 64 128 129 record003_frame017_links_0064 record003_frame017_links_0128))
theorem record003_frame017_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 17 :=
  of_group record003 17 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0129
    Papers.RationalityTen.SharedFrameCatalogue.group0129_facts record003_frame017_indices record003_frame017_graph record003_frame017_links
def record003_frame018_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86682381d81781080975d6e46d26c66bc6af66e5e65d15c35b65a559858f58757f57756f56555d55654d54553d53352b5244743ec3d73c93bc3ab36f2f62e42d82ce2c12b52ac2a429c29428c28227a27326a26225a2502482412201d81d01c91c31bd1b71b01a81a119919017917116916214513e13612f12711e1070ff0f70f00d40d00cc0c80c40c007107006b06a06906206105c05b05a03903803303203102a02902402302201501400f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record003_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record003) (record003.maps 18) (record003.inverseMaps 18) record003_frame018_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record003) (record003.maps 18)
      (record003.inverseMaps 18) record003_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame018_links_0000 (interval_append _ 64 128 129 record003_frame018_links_0064 record003_frame018_links_0128))
theorem record003_frame018_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 18 :=
  of_group record003 18 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record003_frame018_indices record003_frame018_graph record003_frame018_links
def record003_frame019_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x4cc95d2a65149b92d1a618c2a84307209bfc76eeb9d139b720e19bfb796e8db9b53606aed4da6346680ce59ab30606af959aab544a5d4124a4848ed1aa2c44686d0b21041881cfe1f43e07a4f11dd3ac748e69bb314610bf17b2f05ccb61672c0564aa13d26c4bc9410f2144087e0f51e0364690cb1882a45189f1382604a0670cc188308600b2160298520a20dc1b0310600bc1482804808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record003_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record003) (record003.maps 19) (record003.inverseMaps 19) record003_frame019_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record003) (record003.maps 19) (record003.inverseMaps 19) record003_frame019_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record003) (record003.maps 19) (record003.inverseMaps 19) record003_frame019_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record003) (record003.maps 19)
      (record003.inverseMaps 19) record003_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame019_links_0000 (interval_append _ 64 128 129 record003_frame019_links_0064 record003_frame019_links_0128))
theorem record003_frame019_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 19 :=
  of_group record003 19 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record003_frame019_indices record003_frame019_graph record003_frame019_links
def record003_frame020_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x4cb94527a4d49491d12a08c09804ff9fb3e073ee59c73876fadddb836a6cad7dadb52694d159eb37664ca99231d5b2a6147a874fe9d93122944286909a0e412808fe1f83e47b4f21dc3ac73ce49c43766d4d799a2cc58cb015d2b054ca69482864fc9d12a2444708c1001f63dc790ed1ce358678c918a2b8560a61402744d0620c21702d85a0ae1582885009e0d81a83005e0b81502904808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record003_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record003) (record003.maps 20) (record003.inverseMaps 20) record003_frame020_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record003) (record003.maps 20) (record003.inverseMaps 20) record003_frame020_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record003) (record003.maps 20) (record003.inverseMaps 20) record003_frame020_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record003) (record003.maps 20)
      (record003.inverseMaps 20) record003_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame020_links_0000 (interval_append _ 64 128 129 record003_frame020_links_0064 record003_frame020_links_0128))
theorem record003_frame020_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 20 :=
  of_group record003 20 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record003_frame020_indices record003_frame020_graph record003_frame020_links
def record003_frame021_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x3af71ee31c2b7d6f2d4995b2663ec6d8b3085aeb4565ac6582af55c2b3560aa95329f532a594828d510a053e2794a28810da1341c828ff1d73a272ce31c337e6dcd99b035a6a0d019b32e64cc718a3045f8bd9642624b8941232404748d115220430838f91ea3bc758dc1b0344670ca18c2e0598ae1522684b09211c230450620c21742e05b0aa1502784e09a0d41a02f05c0b41482804808c1101502803c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record003_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 21) (record003.inverseMaps 21) record003_frame021_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 21) (record003.inverseMaps 21) record003_frame021_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 21) (record003.inverseMaps 21) record003_frame021_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record003) (record003.maps 21)
      (record003.inverseMaps 21) record003_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame021_links_0000 (interval_append _ 64 128 129 record003_frame021_links_0064 record003_frame021_links_0128))
theorem record003_frame021_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 21 :=
  of_group record003 21 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record003_frame021_indices record003_frame021_graph record003_frame021_links
def record003_frame022_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x21684e1083a0c829fa7b9ed7b1e9799e1741cc721c4701be6edb76cdaf6ada768da06799c669966458c5e96959561575595514a51d4450d425013d4e5354c52d4a1234811e4711a45d13438fa370d935cd534cd0330c8310c02f4b52c8ae2ac9a25c9323c8b21c791d8741c4611745915451130400fc3c0ec3a0e0370d8350d02a0a42809c26090230801f078110400f0380d0300b0280902007018050100300801 } : Fields).get c.val)
theorem record003_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record003) (record003.maps 22) (record003.inverseMaps 22) record003_frame022_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record003) (record003.maps 22) (record003.inverseMaps 22) record003_frame022_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record003) (record003.maps 22) (record003.inverseMaps 22) record003_frame022_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record003) (record003.maps 22)
      (record003.inverseMaps 22) record003_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame022_links_0000 (interval_append _ 64 128 129 record003_frame022_links_0064 record003_frame022_links_0128))
theorem record003_frame022_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 22 :=
  of_group record003 22 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record003_frame022_indices record003_frame022_graph record003_frame022_links
def record003_frame023_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0148.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0148.count (({ width := 9, code := 0xfa7c3d9e8f2783b9daec75ba9d2e772b8dc2df6eb6db0d56933d98ca6431584bf5e2e970b659ac55ead55aa550a75329548a350a7936984aa49208e45a210a82401f8f87a3c9e0ee763a9cce26f369acd26531984be5a2c158a852281309448231047e3d1d8e46e31180bc5c2d160ac542914084401f0f074381b0d06430110803c1c0d0602c14090401c0c050200c0401 } : Fields).get c.val)
theorem record003_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0148.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record003) (record003.maps 23) (record003.inverseMaps 23) record003_frame023_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record003) (record003.maps 23) (record003.inverseMaps 23) record003_frame023_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record003) (record003.maps 23) (record003.inverseMaps 23) record003_frame023_indices (Fin.ofNat record003.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record003_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (smallEmbedding record003) (record003.maps 23)
      (record003.inverseMaps 23) record003_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record003_frame023_links_0000 (interval_append _ 64 128 129 record003_frame023_links_0064 record003_frame023_links_0128))
theorem record003_frame023_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 23 :=
  of_group record003 23 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0148
    Papers.RationalityTen.SharedFrameCatalogue.group0148_facts record003_frame023_indices record003_frame023_graph record003_frame023_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (Fin.cases (record003_frame009_supported hcells) (Fin.cases (record003_frame010_supported hcells) (Fin.cases (record003_frame011_supported hcells) (Fin.cases (record003_frame012_supported hcells) (Fin.cases (record003_frame013_supported hcells) (Fin.cases (record003_frame014_supported hcells) (Fin.cases (record003_frame015_supported hcells) (Fin.cases (record003_frame016_supported hcells) (Fin.cases (record003_frame017_supported hcells) (Fin.cases (record003_frame018_supported hcells) (Fin.cases (record003_frame019_supported hcells) (Fin.cases (record003_frame020_supported hcells) (Fin.cases (record003_frame021_supported hcells) (Fin.cases (record003_frame022_supported hcells) (Fin.cases (record003_frame023_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record003_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00291
