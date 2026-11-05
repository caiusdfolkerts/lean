module
prelude
public import GraphInputsRow31Part00006Data
public import RawFrameSupport
public import SharedFrameGroups042Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00006
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7347267056f56e46c76ac69867666766261b5fd5c95ba5a15965875815474e148a47e47146c46145643a4314214173f83ee3d73c73bd3ac38e38037d36234733132c3243133032f32ec2e82e02c42bc2ac2a829f29a29729428226b25e24723c22f2081fc1f01dd1d51b019f18f18317d16a16616215a13a11b0f00dc0ca0ba0aa09f09906a05d05905305205104f04c04a04804504203c03703403302d02a02702301d01c01201000e00b008007003002001000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0573.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0573.count (({ width := 9, code := 0xd668b3797ca63b0d83be5e6ed70b6592c75dacd52a3499c4aa4f239047a3b188bc52230783401fafa7abb5d0e57137db6d96bb51a2cc64b218cc15f2ed70b559ac55ead552a54ca450a75349849a411a8942a0d007c3d1e0ea7236994bc5c2b93c92471a8c4602d160ac54291409c4c25110803c1d0c8602e1508840180b050200c05018080200 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0573
    Papers.RationalityTen.SharedFrameCatalogue.group0573_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0564.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0564.count (({ width := 9, code := 0x85426110682c0e02ff7e3e9eef57a3c9e2ee763a5cce06ab3194c661b0580bf5f2f578b95c2dd6cb5592bd58aa5429948a250a7d3a994ba592a91482391689442190882401fcfa7b3d1dcea74381b8d86933998c6612f974b4572912888421e8e47037168ac542713094482311084401f0f074381b0c8602e1508840180b050200c05018080200 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0564.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0564.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0564.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0564.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0564
    Papers.RationalityTen.SharedFrameCatalogue.group0564_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7347267056f66c469568367366466265e65564163962d62561b5fd5f65db5d35c95ba5a159658758156d55654853951e4fc4e94e14c74b048f48a47e47647146c46a45f44844243142941c3fb3f63d73cf3c23af39b39138337d36934e33b33031c3012f42ec2d82c52aa2a829f29929729427e25a2232021fc1d51cb19518f17d16616213c11d0f00dc0ca0ba0aa09f09709208c08807e06a05d05905305204a03402702301d01c01b01801501201000e00b008007003002001000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0575.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0575.count (({ width := 9, code := 0x1bedd6d763acd3e8f3f9acbe5b2b91c863f1d8dc4613017fbf5f2eb72b6da6cf64afd66ad4da450a813b984b251228fc7235198ac52271288c32110481c0a00f97b3c5daec75399c2e06cb59a0cf65b057ebc5bad968b15729544a14b2551a8c431fcfa7737988b25627924904622908803f1c8d4662f170b44e210f06430170a048200f0682c1007018080200 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0575.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0575.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0575.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0575.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0575
    Papers.RationalityTen.SharedFrameCatalogue.group0575_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0566.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0566.count (({ width := 9, code := 0x168b3d96c75fadd66ab51a7d3a9b4aa4d228f46a2506813f9f4f26f3598cb6572992c823b178943617077fbedeef277bb1d4e973395c8e371381badc6db69b0d368b3592c863b1180bf5dae166b257aa14ca34fa79389a4c2451e8e42a10fa7c3c1c8e06c32964a44f249108641200fc7a3c1b0c8602c158a8481e0d8582a14098441e0e060280e06018080200 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0566.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0566.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0566.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0566.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0566
    Papers.RationalityTen.SharedFrameCatalogue.group0566_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x108882e3e85eb8e896d835a9a48cdf6663301958c756303115874c205d3ae4d682b3158c2b8d52ca67514a8493c29a94bda54d24a8e145922610d48353fa9fa0f8a7b13d31e54f187783a09cb0e2270637619cccbe60d2fe9790b5e56229993d49bc4ad23a911c83e3f11d68df86c83361808b0456829113e89c84c224c11b88383f21f30e7072033c1980c485b42ce14a09a84481fc0ef071033816c0a504f824811c084036017c0b605502a0130068027011807403801b00c0054024010007002c0100070018008002000 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1040.count (({ width := 11, code := 0x42b8510760cc0e80aff5fa3ec7d4f9df13d57a0f2de4bc3768ec1d2ba3736e41bfb776d4d95adb5068ece998b22634c5185b005d4b9d6e2d65a8b41672c9578add592b0550a5d49a8850ca013ba664b89452624246e8b910a184067ecfa1eb3c0740e71c337a6e8db9aa32e5e8b39642905089111f2204087f0ec1b22ec570a1130230450871082003e0720c41582904c09610c198270460740e01b0300540901001c02c0400700600800800 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1040
    Papers.RationalityTen.SharedFrameCatalogue.group1040_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0574.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0574.count (({ width := 9, code := 0x143a15027d3a9b4d2612c954a651259248e45218fc72371a8cc5e230f85c1e0d0581bfdfcf97abc5e0ec72b8dc2dd6e369b0d76a349a2d067b3594c96431d8ac05f2e96cb55a2c95cad54291409f4da51248f4622d1287429fcfa7c3b1d4e06f3619cca622e954a24e259208e44219087e3e1b8cc602b150a4441c0d0582a14098441e0e060280e06018080200 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0574.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0574.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0574.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0574.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0574
    Papers.RationalityTen.SharedFrameCatalogue.group0574_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0565.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0565.count (({ width := 8, code := 0xd9d8d7d6d4d2d1cfcdcccbcac7c6c5c4c3c2c0bfbebdbcb8b7b5b3b2b1afacaba7a6a4a3a29d9c9a9796959493908f8e8d8c8b898887868581807e7c7b7a787574706f6d6c6b666563605f5e5d5b57555452514e4d4c494846433e3c3a3836353332312f2e2a26242221201c1816141312110f0d0c0a09070603020100 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0565.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0565.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0565.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0565.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0565
    Papers.RationalityTen.SharedFrameCatalogue.group0565_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record001_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00006
