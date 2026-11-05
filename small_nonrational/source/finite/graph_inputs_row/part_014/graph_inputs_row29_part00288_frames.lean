module
prelude
public import GraphInputsRow29Part00288Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00288
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x67466c6325f05bf5ad5a855d5245195114c94bc4b149e49048547f46b43b3f93c43b03ab37033d33532f2ec2e22db2ce2c32bc2b62a927826d26424622d2242172101ed1d11b91a519117e17416414212d12511e1060fe0ee0e00d50c908107f06b06906706405b05a05705505105004f04e03903703503202902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65a6566335f85bd59d5955555185044f64bb4b44ae4a249b4954904834624223e63c83bf37b33c32931d2e02d82d22c62c02bb2b72ae28928027524922721d2061f91d51c41b119818617216815513e12c1211140f60ec0d80c50bc0b808608306e06c06a06705f05e05b05905505405305203803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x518a2b3be5e48b8ef1d22641d82702df03da7a4f19df3b9764e99bbb3b612bd578ac352aa2940a5c4b0949242404788dd1620c4047e4ee1c33726a0cf1842ea59cac94e2764d49291320a3f47b8dd1aa3205d8b616021c4286e0da1ac340600be1742d8570ac1542a03906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd1567db029654a89525a8e93228fa46b22fd06081c4061fa4fac7c73db9e54dac5f62aa945ca0c45d1e30e887162fc1740b6056a2a21498a0c4c223911908ac41e1fa0f9878c3b81c20da069832e18a0bd85d42ce1520a204f426a12108c84301fc0f6078024811a07103781b40d406103001740b605702b01540a803901b80d4064029014009404601f00f007403801500a004c0220100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x47e8f114210bf87d2f91dcb93712e0db0b5a6aad35a2b3f676cbd88adf570aa952a764a492922222436855052033fc7e8f81d5398710d619731e610c01672ae5249c92922e440808f21d03906f0cd18c2ec580ac1501fc3d8680cc190308580ae1502904e09a1302583906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x4a794121e3143c85308df6bbf762e85b4b616b0d2da233e674cc5922fa598ac9572774a09111d2063fa7d4f41e03b675ce71bb36e6c4d119531e60cbe96c2c0550a193624e4848b1021ea3c0738d21942f4590aa1482003d8670ca18c308580ae1502904e09a1302583706a0cc1802804e0941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x78e7867396f36be69e69564e6025ec5dd58557d57356355654c5405274ef49844d42c4233d63a539538b33b32e32430b3002fb2f12dd2b12a729927224f2472312282071f11dd1c81ba1a219818116415214713d11a10d0fd0eb0e30dc08c08706e06c06a06705e05d05a05805405305205103803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x381d8f8c685d1285d4069ae4d3a68130896f4b425612a291b489a4311fe8f747823a91b883234199b8bc65d22e015d0a7a52b28193c88ce454221108c8224011f88f446e83631a88c1459c2bc14a0a0c3f01e50e986d03441920c105882ac14f0a4050427413308b84101ec0ef074824811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3bdda26cfb605293d4749b64d1264528c90c47d234917e83040f2030fd27d83e39edcf2a6d628d941890446e22e90487b03c61cf0e2c5f82ea16c0ad45482931418984472232115883c3f41f30f1877034c19e0cb862830417b0ba859c2c01590a9052c28813d09084301fc0f7078024811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0xe099131c5eea5d48a714dc9ad2fa564a692d2423245c8ad1322243e8750ba03346674be97a2ee5acb115f2ae5509f13a26e4c89712b25248c8a11121c4087c8f61dc3ac6a8d119c324628c21802e85b8b616a2d0598b215c2ac548a814e218408690c81702d85a0b015c2a8510a013c270370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xeeda934b63cad55728d514a1d3da724de99d3224e49491d2123e4768e519a1835e6a0c39843025d4b61692c2578a41442824f09c1352664b48f11b230430819001f03d46f8db1b034c678cc194310608c017e2f85e8bc1702d4598b21622384486d0d01802f85e0b816c2c8550a814c290370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x28796e5891218855f87d5f37a1df771d4745bc6e1b56c1ac6a5a76859c5c16d5414d52d404dd344b1294511043508411013fcf93ace8398db348cf31cc42bcab2a0a327c9c268942449023c8e2348c2208520c822046f1ac5d164511404f1344c128461144410c360c82a0a4280982508c1f0781d0701505013044100380a0240801c060140400c0200400 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6df67366c6325ae5a857156655d54152d5245185114c94bd4b149e49148547f46b43b3b13ab38137837035934533d33432f2ec2e42db2ce2c52bc2b62a927826d26424622d2242172101b91af1a519118817e17416415814c14213712d1251060ee0e00d60c908107f06906405c05b05a05805705505105004f04e03703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xfb5db3b072cd7dacb3665cca18b309606be17a2cc58cb015bab0554a9d4e28b4a693d17a2c452865062063f67d4e59c63826dcd71a9348670c117c2ec598ae15929e5248f918226420818fe1f23c0748e41bc360690cc1702984f09a12a1c4368600b8150298520a21402784b094124240370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x12763ec788a0fa9f23c477eee5d3b9a726e21c1b616b6d55a6b4667eced97b11556a9541a7d4ec9912c2524929111121c42a829021fe3f47c0ea9cc3886b0cb98f308600a49422724a4901172204047e8f71e43b4740e419a2ec580ad1501fc3d8660c21642c0570aa1502904e09a130258370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame008_links_0000 record001_frame008_links_0064)
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
def record001_frame009_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0980.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0980.count (({ width := 8, code := 0xfdf6f5efe8e7dddbd9d6d4d2cfcec4c2c1c0bebdbcbbb8b1b0a6a4a29f9d9b98978d8b8a89878685847d7b797674726f6e646261605e5d5c5b5a5958575655524f4e4d4c494844433b3a39383736333231302d2c24232221201f1c1b1a191211100f0e0d0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0980.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record001) (record001.maps 9) (record001.inverseMaps 9) record001_frame009_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0980.localPairCheck (smallEmbedding record001) (record001.maps 9)
      (record001.inverseMaps 9) record001_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame009_links_0000 record001_frame009_links_0064)
theorem record001_frame009_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 9 :=
  of_group record001 9 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0980
    Papers.RationalityTen.SharedFrameCatalogue.group0980_facts record001_frame009_indices record001_frame009_graph record001_frame009_links
def record001_frame010_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0978.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0978.count (({ width := 8, code := 0xfbf5f4f0eae9dfdddbd9d7d5d3d2c8c6c5c3c1c0bfbdbcb6b5aba9a7a5a3a19f9e9492918f8d8c8b8982807e7c7a7876756b696866646362605f5e5d5c5b5a565351504f4b4a45443c3b3a393837343332312d2c24232221201f1c1b1a191211100f0e0d0a09080706050403020100 } : Fields).get c.val)
theorem record001_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0978.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record001) (record001.maps 10) (record001.inverseMaps 10) record001_frame010_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record001) (record001.maps 10)
      (record001.inverseMaps 10) record001_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame010_links_0000 record001_frame010_links_0064)
theorem record001_frame010_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 10 :=
  of_group record001 10 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0978
    Papers.RationalityTen.SharedFrameCatalogue.group0978_facts record001_frame010_indices record001_frame010_graph record001_frame010_links
def record001_frame011_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xafaa3ea319d48f48e789388687b84581c8097de7cd75073a7267006ec6da6c86a266a58f58253e53452a4fa4da4cc4aa49c4364244143f53e53d73c73a837936d36032d3052f52d72cb25a24823821a2081f91e91cd1c21ba1ae1a019118314611c0fe0f30e808c08706d06806005f05e05c05b05905505405305203703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record001_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 11) (record001.inverseMaps 11) record001_frame011_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record001) (record001.maps 11)
      (record001.inverseMaps 11) record001_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame011_links_0000 record001_frame011_links_0064)
theorem record001_frame011_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 11 :=
  of_group record001 11 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record001_frame011_indices record001_frame011_graph record001_frame011_links
def record001_frame012_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x1746b3d5ba552fe5d48e91521a38c638bb13623414819015fc3ef7ccf7de9bb0660c957baf15d6b3d5f2b4546a71312584a09051b22d44884cfe1f83e4750e11bb350684b395e2ac5189d9322524608890d2104087e8f81c2340630c11782043e0680c61702d85a0b015c2a8510a013c270370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 12) (record001.inverseMaps 12) record001_frame012_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record001) (record001.maps 12)
      (record001.inverseMaps 12) record001_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame012_links_0000 record001_frame012_links_0064)
theorem record001_frame012_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 12 :=
  of_group record001 12 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record001_frame012_indices record001_frame012_graph record001_frame012_links
def record001_frame013_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6ff65e65160e56e56052b5225164f24de4d24bd4af4654584494304254184103fb3d533232a2f22e82e12b92a229c28327822c21d2101f71e91e01d71c21ac1a81a218b17c17716a16413d13713112912411e11811010c10a1051000fb0f60e00cf0c50c00ba08407f06806305b05a05905705605405004f04e04d03703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record001_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 13) (record001.inverseMaps 13) record001_frame013_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record001) (record001.maps 13)
      (record001.inverseMaps 13) record001_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame013_links_0000 record001_frame013_links_0064)
theorem record001_frame013_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 13 :=
  of_group record001 13 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record001_frame013_indices record001_frame013_graph record001_frame013_links
def record001_frame014_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x16729f537a252d25847f8ed1a62743886106e09bdf7b0f39df3b475ae91c9b6f5e0bad63ac457caa54aa8d4f69d12023a45e8910d2114127e4ef9d839e6d8d31a332a634ad1532924e09712823e44c869092063f47b8f11b63205e8b91662083e86c0d01802f85e0b816c2c8550a814c290370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 14) (record001.inverseMaps 14) record001_frame014_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 14)
      (record001.inverseMaps 14) record001_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame014_links_0000 record001_frame014_links_0064)
theorem record001_frame014_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 14 :=
  of_group record001 14 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record001_frame014_indices record001_frame014_graph record001_frame014_links
def record001_frame015_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0542.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0542.count (({ width := 9, code := 0x4d64f2691452270a8441602fe7e3ddeaeb74b9dc8e27037db8da6632d84c05eae56cb457ab546a14fa7134984ba511a8b44211027f3d1e0dc6c3519cca633117cbc5d2e16cb4592a948a04f271289246228f4783b1d0e47034198c8622f170984a2411888421d0e06c341309044200f070281208038180a04018080200 } : Fields).get c.val)
theorem record001_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0542.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0542.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0542.localPairCheck (smallEmbedding record001) (record001.maps 15) (record001.inverseMaps 15) record001_frame015_indices (Fin.ofNat record001.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record001_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0542.localPairCheck (smallEmbedding record001) (record001.maps 15)
      (record001.inverseMaps 15) record001_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record001_frame015_links_0000 record001_frame015_links_0064)
theorem record001_frame015_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 15 :=
  of_group record001 15 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0542
    Papers.RationalityTen.SharedFrameCatalogue.group0542_facts record001_frame015_indices record001_frame015_graph record001_frame015_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (Fin.cases (record001_frame009_supported hcells) (Fin.cases (record001_frame010_supported hcells) (Fin.cases (record001_frame011_supported hcells) (Fin.cases (record001_frame012_supported hcells) (Fin.cases (record001_frame013_supported hcells) (Fin.cases (record001_frame014_supported hcells) (Fin.cases (record001_frame015_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdfd68c33e99c4b42596ac5d512a4951ca8953228d146022b113486442120c104280b3fc9f58f907b73ca1838bf25e32aa9454a0a4f122e8e747183781b30cc061c2fc1768b5c58a2a214a0a0c4c023911908ac3f41dd0eb07403921c20dd86d035a1a60ce865831e17c0ba85982a414409e84d424211908984301ec0db04681ec0da06a03081800b605a02c015c0ac05402180d4064029014008c04402000f807803801500a004c02200e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb65af0ad4ac5a21a15a0f9b297e96d95e90986184a8368247f77d47c07ae79477f75574272b6fd66e6616596085de5d55c95774ee4e04d24c449b48247746b45744842841d40f3ef3bd3ae3a43412f92e92d82c72b72ad2a12932862732632532252151f11cd1b51a819716b1561451351030cd08d07b06d06a06106005b05a05805705605404303503202902802302202001f01e01c01501401301100e00d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x68063e6326255be5b85b357855a5535465114b44aa49f49748047046645e45344643042a42040e3b63b13ab37035234833f3092ac2a029628f27826625f25624823e2282202172061ee1e71e11bc1a319c19618f18918418017a17316a16415c14d14513a12711d11610e0f90f20eb0e30d30b808107206706405b05a05505405205105004e04003503202902802302202001f01e01c01501401301100e00d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record002_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00288
