module
prelude
public import GraphInputsRow28Part00012Data
public import RawFrameSupport
public import SharedFrameGroups011Checked
public import SharedFrameGroups012Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups027Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xcea5a2acd95aeab054429e13b29ca4b5a51123890c46c22f115c899449222cdec6e734819c8c966392d09648a7651d27b139096249624411d48de4691dd8ea06803191778b685722a914c89e84d625b11e087441c1d60e306d832e1880bc056427412b07b83c01d20e206d835015e09b03c01d00e006e03581a80d2065030817c0b805b02d010007803801b00cc06403101680a404e0240118088030014009003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x31958a0c3950027ad3a89984c925b92c29524a624f926e930493a45120c8fe47c23c51c466b32b18f8b5659929e14609e64e125f12b093448622a90c88444122010f8067832a1668aa450827212788f44562170f3070c3661a30c985c42ac14f0a404e826612c08f04402140dd04d824c11c08c03c01c00d606903281840be05c02d81680b205802b81540a804001c00cc06202d014809c048023011008404001f00e8070030014009003c01c00d006002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33e19c2cc751ba89141a97d4b5a42d1ce8c0456a2210ec864428207cff67e83ec9f20f4c50327813648924371eb8ecc7183791aa0d0866031c1758b1c5682a514a09c844621d0fc87b03ba1d70e487083761b20cf86443121830be05b42c01590a9051027a13609404682260e204d824c11c08c03c01c00d606903281840be05c02d81680b205802b81540a804001c00cc06202d014809c048023011008404001f00e8070030014009003c01c00d006002c014008003801800a0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xd21a1b39556a994e2835029c5362654c69752d2574a492d22a4147e8f11a9a5340658be97b2d6598af95d2ae550a894c28a4fc9d93926c4bc8a1122043f47b0f41dc3ac740e31b8358690d019a318608c017e2f45e0bb1722dc5b0af12e23c450880ec1b8348670c617c2e85a0b21602b8560aa14c290400700cc1882d05209c120230440841001f03a0700c01402403c0700d01802c0500800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x105607c08742e71cbb756e2d59a5340678cc596b2a64ec5985b035febe97427a4ee9c926a4645c8950ca1641882102a023e278ced1d63a070ccb9912e659caf15a2a4534a414426649c9091b22c4247f8f81e43a8718dc1a23186089a0fc1f03c0760d41943005e0b41582a0510a013c2704d0981282483d0700cc1882d05209c120230440841001f03a0700c01402403c0700d01802c0500800e0180280400600800800 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0843.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0843.count (({ width := 8, code := 0xc9c8c6c0bfbdb7b6b3b2b0afadacabaaa7a5a3a2a19e9796948e8d8a898786848382817e7c7a7978756e6d6a696766646362615e5c5a5958555352514f4e4d4c4a49434241403f3e3d3c3b383534333231302f2e2c2b2a2928272421201f1e1d1c1b1a18171411100f0e0d0c0b0a080706050403020100 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0843.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0843.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0843.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0843.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0843
    Papers.RationalityTen.SharedFrameCatalogue.group0843_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x196ac8d632b141878a5051428013d69d74bea5852b49524a62515260928491246d20c8ff47ba3c4d7a6963359958c8256128c14149e64e1268926890e47723390c88464112010bc855229614209c84c422b10c08203f01c30da06883261560a78520274133096047822e10a077828412608e04682300fc07003581a80d206503081780b805b02d01600ae05602a815008c03801980c806202d0148098048023011008003e01e00e8070030014008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1aaad2867c3385994a8652fa8dd448a10499239d1a88c0456a2690c885142120c0ff67e93ec1f20aa452b28193c09b83fe1d98e807183791b30cc063a30e17e0b1c56a2a414a08203d81e50ee875c3a01bb0d986b434c1910c506082f81600ac854828813d09b04a024211307b828412608e04682300fc07003581a80d206503081780b805b02d01600ae05602a815008c03801980c806202d0148098048023011008003e01e00e8070030014008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1b1357690d0d9e2c5574aad5329f4f09b134a654c69812ba534a293922a4247c8f0df9b434a680cc9722cc58caf95d2b4544a694b2904fc9e13826c4247e8fa1ec3d0788e81c83886f8d61a633c668c11802fc5e8bc1762e45c0b61642744788a1122203e06e0d21a0338630be1702d0590b01582a8540a6148230380660c81882d052098120230440800f81e03a0700c01402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x21041781d02602bb9762e9dd1b9e6d6d55a6b46680ced95b24640c61832ff5f2bd143a7f4ec9c936a3f45c8a11121f434839032043fe7c8f69ea3cc644be9762e25acb295729c524a193525e4ac93911214404798ec1cc35c688c515c21c4187e0fa1f03906a0ca190318610ba1682c0570ac150298520a2140218380660c81882d052098120230440800f81e03a0700c01402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x1f9bea7bef65e9b8d706df5bbb70684c8d8cb11616c1578ae75c0b6561aba564aad2ca4f48e9051ea1440e808fe1f63ea790f01db3aa704de1b83645d8ae9572a4530a413b2684c49512323e4688b1011f83d8760e61c0354678c61622103e0780ee1d8380680c818c3105e0b415c2a8540a61442804f09c134208360620c01782c0500941182204207c0f01d03806c0c01402203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0588.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0588.count (({ width := 9, code := 0x1c6e06f371b2d5693419ccb623017ebd5e2ed72b85bad562b0572b548a14fa75349347a39188b452210e8642200fe7d3e1c0d86b349a0ce653218cc25d2e168b253291449e4e2692c94482310882401f8f87a3c1d8e872371a0c86230178b85a2c158a85228138984a23100783a1c0d86832180b8582811078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0588.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0588.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0588.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0588.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0588
    Papers.RationalityTen.SharedFrameCatalogue.group0588_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd16684b3e99e8ced56baac1510a7853325ad28891c48623e91dc8e747023491968c445b22bd1508a134819c8c9663931414eca3a4f6272134c98e4c025c92b094a49e248122490447c1a00c645de2da1638ae455229913d09ac4b623c116887441c1d60e306d832e1880bc056429413a095825c12608e04682300e807003581a80d206503081700b605a02c81600ae05602a815007803801980c806202d0148090046022010808003e01e00e8070030014007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcb7646b1958a0c3c52928a14009eb4eba5b92c29524a6251527c937498248923691448323fd1f08f135f9a58cd665632094f0a304f3270934497c4ac24d11dc8ce455219108c8244021668aa4508272131093c47a22b10407e03cc1c30da068c3261560a78520274133096047822e110085025c12608e04682300e807003581a80d206503081700b605a02c81600ae05602a815007803801980c806202d0148090046022010808003e01e00e8070030014007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1108.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1108.count (({ width := 9, code := 0x12b9448e45208a446190b84bf9f6f67abcde2f077bb5d8eb74ba1cee66cb59a2d06730d80bb5d2e16cb55a2c962b0572b558ab4fa712e964a249229047235188a44a210e8441a09007f3f1f0f67a3c9c4da6833998c25d2c15cac52271249047231148843211047838198c8622d148904622108803e1e0e8703014078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1108
    Papers.RationalityTen.SharedFrameCatalogue.group1108_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd5769433e19c2cca544297d46ea24508242d1ce8c0456a269110876432210906081f3fd9fa4fb27c82aa14aca064f026e0f5c76638c1bc8d986a83421980c385f82eb1638ad454a2940fc87b03ba1d70e807243841bb0d6869833e1910c5060c2f81600ac854828813d09b04a024211a089825c12608e04682300e807003581a80d206503081700b605a02c81600ae05602a815007803801980c806202d0148090046022010808003e01e00e8070030014007803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3636aed21a1b3c58cae955aa653e9c5362654c69812ea5a4ae9452724b48a9091fa3c3806d0d29a03325acb315f2ba568ab9542a252ca414527e4f09c9362043f47b0f41e23b8758e81c437c6e0d61a6340668c11802fc5e8bc1762e45c0b716c24c4788a1122203906e0d21a0338630be1682c8580ae1582a8540a61481e0380660c81882d052090118220420800f81e03a0700c01401e0380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record003_frame005_links_0000 record003_frame005_links_0064)
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
def record003_frame006_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1107.count (({ width := 9, code := 0x12b9448e45208a446190b84bf9f6f67abcde2f077bb5d8eb74ba1cee66cb59a2d06730d80bb5d2e16cb55a2c962b0572b558ab4fa712e964a249229047235188a44a210e8441a09007f3f1f0f67a3c9c4da6833998c25d2c15cac52271249047231148843211047838198c8622d148904622108803e1e0e8703014078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record003_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record003) (record003.maps 6) (record003.inverseMaps 6) record003_frame006_indices (Fin.ofNat record003.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record003_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record003) (record003.maps 6)
      (record003.inverseMaps 6) record003_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record003_frame006_links_0000 record003_frame006_links_0064)
theorem record003_frame006_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 6 :=
  of_group record003 6 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1107
    Papers.RationalityTen.SharedFrameCatalogue.group1107_facts record003_frame006_indices record003_frame006_graph record003_frame006_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcc96333141876a64500a7ad3ac9984c225f52ec96d4ad254d29894449824a124491b486a4191ee8e336999b0cac6402d595d0ac254f29d94149e84e1268126890e477233910c8644111f08cf060a2f21700b3052c285139098445621810407e03a81c30d105c82ac14f0a404e826612c09284781fa0ef048823c11c08c03701b00d6069032817c0bc05d02e01680b005702b01540a803601a00cc06202d013809804a024011008003e01e00e8070030012008804001e00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd7067cb385992a9d51c289141e97d4a324c923c90a46a230515a89943221450848304069fecfb07a72b494109e04db22490487fc3ea1eb0e8071a3791b28cc063a30e17e0b6458e2a4139888c41e20810087e03ca1de0eb873c3761b30d686983301910c105b82c01590a9051027a13609784a020a0f7048823c11c08c03701b00d6069032817c0bc05d02e01680b005702b01540a803601a00cc06202d013809804a024011008003e01e00e8070030012008804001e00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x36a692d0d9dacd558a994f2834f69e13aa704d299931a5f4ae94d28a4e4909151f23638e698d01982fa5d4b916f2d458cb015d2b2544a694b2905089f9382604508610920c4047d0f71e83c0740e41c437c6c8d619e31c608c017e2f45e0bb1742e45a0b211a22c450880d81a8348670c61742e05b0b41602b0550a814c290360680cc1882d04e098128240440800f81e03a0700c0120220400780d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb1fad3ac4ab39c096c95d94d8f78c38b18a889686484b8378237f77e97d47c07967817577146125d45c85b856a54053052751a4f14e14d34c349b48f48247745944a42a3fe39636b35834d33f30c2fa2ea2d72ad2a02932862652552332031e21d51cd1b51a819818717812510409108f08e08c06e06c06b06906505f05e05d05c05a05805705605505403603403303102d02702602502402202001f01e01d01c01801201101000f00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x5c7b45662c94ff9b5352654a893324a46c878f11c2354648a713623c418690ba10c0f698c998eb135b6b115e2b755aa51462864f899d3025b4ac9111da2c434770e31bf3706b8ca98e30c5f4b41612ba55ca213d25a46c871082063e47a0ee1d0388638bb1021fc3f07c0ce194320620c217c2f05d0b81682c0570ac1542a0360680cc1882d04e098128240440800f81e03a0700c0120220400780d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame005_links_0000 record004_frame005_links_0064)
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x65e63162461658155254553c5094ed4e54df4d44b74ab4a049648047747046645544843241737934733e3343012e62dd2d72cc2af2a129728e27826f26625f24a24022a20f1dd1cb1c51bf1ba1aa1a419d19518417f17a17316615e15213f13312c12711d11610f1070ff0de0d408508308208006806606506305f05905805705605405205105004f04e03603403303102d02702602502402202001f01e01d01c01801201101000f00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record004_frame006_links_0000 record004_frame006_links_0064)
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd4068f33ed9e8cec5a2abad512a78532a7652fe91d48623e51dc8e747023491968c445ea2d915089337b1a8cc986393139684a9c4f7272134898e4c025c92b094a49e24b92409044701dd8d5c5e02da1630ae455229913d09ac4b624c11e08743e41d60e306d832e1880bc05a42b213a087825c12208f04702300e806e03601ac0d206502f81740b805a02c81600ae05602a815007803601a00cc06202d0138094048022010808003e01e00e8070030012008003c01a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd25664b1998a0c3b56029914029eb4eb26612ec9534a6251127c9374982489236914486a4191f08e339b9b4ccd865632016aca9e4f4270934097c4ac24d11dc8ce45522190c88243e119e0b8050a272130893c47a22b10407e03cc1d40e1868c2e41560a78520274133096049423c11007e825c12208f04702300e806e03601ac0d206502f81740b805a02c81600ae05602a815007803601a00cc06202d0138094048022010808003e01e00e8070030012008003c01a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1108.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1108.count (({ width := 9, code := 0x13196c92451f8d45a1b0b8441200f77abc9e2f077bb5d8eb753a5cee46fb6da4d066b258abc5d2dd6cb55a2c962b057ab958a952a85309649a49229047235188b452210a8441a09007f3f1f4f87a3b9c4d66934198c25b2c960ac522612892472311488432110478361a0cc622d138944822108803e1e0e87030120803c1a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1108
    Papers.RationalityTen.SharedFrameCatalogue.group1108_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xde36b833e59c2cc9580aa75470a24507a5f523c8c1456a265110876432210906081f4069fecfb27a72e695a4a084f026d91247d438d1bc8d946a83421980c385f82eb16c8b1c54a27311188043bc1d70e787243841bb0d6869833e1980c8860c2dc1600ac854828813d09b04bc25011a082825c12208f04702300e806e03601ac0d206502f81740b805a02c81600ae05602a815007803601a00cc06202d0138094048022010808003e01e00e8070030012008003c01a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3856d4d25a1b3b5d0b35562a653ca0d3aa664c697d2ea5a4ae9452724b4909151fa363c471cd31a03305f4b79602ba564ab9542a252ca41452844fc9c9302284187b8f41e03b8758e81c437c6e0d91ac340638c11802fc5e8bc1762e85c8b716824c4688b1142203906c0d41a4338630ba16c2d0580ae1582a8540a61481e0360680cc1882d04e094120220420800f81e03a0700c01202003c0680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1107.count (({ width := 9, code := 0x13196c92451f8d45a1b0b8441200f77abc9e2f077bb5d8eb753a5cee46fb6da4d066b258abc5d2dd6cb55a2c962b057ab958a952a85309649a49229047235188b452210a8441a09007f3f1f4f87a3b9c4d66934198c25b2c960ac522612892472311488432110478361a0cc622d138944822108803e1e0e87030120803c1a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame006_links_0000 record005_frame006_links_0064)
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1107
    Papers.RationalityTen.SharedFrameCatalogue.group1107_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
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
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x60d2b0d4c6a424bca4511fa887439a17109c840418a07101c8003f89f9cd7c67d32e9870c065fe2c71550a724ff27c13b894a49024091948b845121b10b484441a1e78e786f836d19f0c7061a2fd17b09e04ca24c11f08ac4242040fd068c3001760b0053c28a12f09304602120f904a02400e6070036018c0c005c02b01540a803b01c80e006a03401580a8050026012008403c01d00e005c02c014009804001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x74eb919bbad8669bb435a0cb7c5982bad57aaaa543a84138897f4a8a4f92368c345e22811326f73711b58cf66262d11634b02526268929093a48823a91bc62a2a9133891c47822a10e88243de1e40e306102c81590a384e824c10c08083dc1d20db06a02e81680b3053028013e07103801b00d606203081740b804401d00e406c03301900ac054027012008c02a00f00600280100070030010004001 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x60d2d85560a5051da62d2f0926489a3d911085c428a0f906081c4089ff8fe07e738a9abccd464e304980cbf05722b1154ca3a50d27f13e09d24df24891a08b445021c90ac84241a1e78df463a2f61780ae4516277132896c47a22b110880c3f41910c005dc2d614f0a304e824c11807c03a412809004101f00de06b032017c0b605802a815009404401c80dc06a03301600a804e026011808404001d00e005c02c013009003c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x71c6e065e61557f55252e5034d74b049a46e42e3fc3c23a837436936435133d3293173092fc2f12cb2c22bc2af27125624a2452222121fc1f11e41c01b71aa19618f17a17216715f14313711d1110eb0e10d70c50b30a90a209a09708e08807006905a05905505304704604204003e03a03703602c02b02602502302101f01e01401301101000d00c00a008006005004001000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5eb5b553650048646644e43741a4063fb3d33a237532b3102f02eb2e62c82ba2a42972892762702542512472301f81eb1e61e11b51a719919218415e15b15514c14212311c1161101030fd0f20ec0d80d20cd0c30b90b60b10a80a309408a07606c05b05a05605404a04904504204003a03703602c02b02602502302101f01e01401301101000d00c00a008006005004001000 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x2b8d4198b27e08bf27aeeedcc37e6e0cd580ad3522a0531a5c4b493922a3a4608890c2133ec7bcf51da364688ce9972f45b8b215c2aa4fc9e93725e4ac8a10f2124107c0f21cc380660c81862dc560a91482784d88e10e1cc3685c0b615c2a84b094114210400740dc1b02c0560981282304207c0f0140260440800d0180280400600a01000800 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1d94e4771b3829b0ed7669bb4c19d4b8f597ac6d5b0ac3557a97d4469c34d7a5b12ae943479a3451948a74491c1cdc26d032f992cc706222d91630af650a27b138c99a49624792048d22b91548a644e826512408e041c2000f687843ac1c60db06443041650aa84ac23a10a07f03dc1e00e906a02e81720af053029413607303901b40d406403181780b603801b80d40620290140098044011006002c0140070030014008001 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x576ab154e4a364aba4c91ca8ab42920fd05e81f4051fe8fd27c53db1e9cf2a5b92c894f8a044231ff0ec46ee31e1858bec5d62d61630ad4522282139898448022b10d885041e20810087c43d41dc0ea87243681a50cf86403141740b7059c2b214b0a184d825c12108904141fc0ef07482400e607003681b00c606002f01700b205602a815007603801a80d0056028013009004201e00e807002e01600a004c0220100078030016009004001c00c0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x67566463b61b5c35b158a56854053a53553052852251d50e5075024fb45f44d4203ff39f38a36133e31731030b3072ff2f92f42e62e02db2d52b329427926e26525925123b23021720a1f21d81c61bd1a819f17d17516915514413a12911e10b0f20e10d50c60c108a07106e06b06a06105e05c05a05705405305203903703403302b02802602402101e01d01c01701601401301101000f00c00b009008007006004003002001000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x86d0b60b40179ef19d4b906e0da5b1b5f6b2d49a7b40670cc996ae65bcb0d56a7c4e69652122543a8650a20d40e810fa1ed3ce788e69bb3686c4d61a533e654c81822f45c0af9502984fc9d92523e464861001ee3b4730dc19c3005d0af1501f8330640c41842d0570aa14c2804d09812c1c8360660c81502804c0901081e03a0700b81602804c0881001e0300580901001c0300400600800800 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
def record017_frame004_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x52fa9293fc9ce49fa46118a88e419207501c7fe3f49f68fa47a83c89dfceda65832217e8b9a54929393949744712309158892439217109880c3f61f48f7473e3771b38d846a033a1920c105ea2d71640ac44f025f12908e44622000fa079c38c1a80cd86142f01640a184902300fa07582400e607003681b00c606002f01700b205602a815007603801a80d0056028013009004201e00e807002e01600a004c0220100078030016009004001c00c0040018008002000 } : Fields).get c.val)
theorem record017_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record017_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 4)
      (record017.inverseMaps 4) record017_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record017_frame004_links_0000 record017_frame004_links_0064)
theorem record017_frame004_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 4 :=
  of_group record017 4 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record017_frame004_indices record017_frame004_graph record017_frame004_links
def record017_frame005_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x8650a208c017a4f15d6b9e702dedbab716d8d9db13576a2d35a32ea5c2b05572784d29251b21a428839052034007ecf89ec3d078ce79c136e6c8d51a033462cc11752da580a71462844dc9911c22c4387e8f21d63886e8d71922e4590a61401f0340670c818c2e05b0b21602a8520a21401c8370680cc1502804c0901081e03a0700b81602804c0881001e0300580901001c0300400600800800 } : Fields).get c.val)
theorem record017_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record017_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record017) (record017.maps 5)
      (record017.inverseMaps 5) record017_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record017_frame005_links_0000 record017_frame005_links_0064)
theorem record017_frame005_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 5 :=
  of_group record017 5 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record017_frame005_indices record017_frame005_graph record017_frame005_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (Fin.cases (record017_frame004_supported hcells) (Fin.cases (record017_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x25e52a694549fa4bd2308ff46ca31514488e419207d01c7fe3f59f68fa47aa3c89dfceda5802ad9538a9253b29394489e44e526392e88e246322b112487642e21310207ec3e91ee8e7c6ee3671b08d406743241820bd45ae2c813c09b04be25212308e446221210007d03ce1d60e306d43501850b204902300fb07582400da06403181840c005e02e81700b205602a815006a02c01580a4050026012809004201e00e807002e01600a004c0220100078030012008003801800a0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x26d53409904c4a6112fa9764b3257d2a294a494a48523491448624151fe8f0474a38d1b85f72e0165cb085742b0953ca52516279137c910476233115488443121190047e03e11e88e206a232818a8c145e42e015d0a9c50627010c881c3ee1e60e987083681920c085c82c41560a7852028212c08b83f41ec0e907182400da06403181840c005e02e81700b205602a815006a02c01580a4050026012809004201e00e807002e01600a004c0220100078030012008003801800a0040018008002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x27213229694aba51926491e47c239517e8ab429210505e81f4061fe8fd27c73db1e9cf2a49422e90d48464121ff0fa87883b11c58ddc63c30d17d8bac5b02c615a8a4c504273130890045621b10a083c4102010f887a83b81d50da06b034a19f0cb864031417b0ba05b82ce1600ac854829613609084141fc0f007482400da06403181840c005e02e81700b205602a815006a02c01580a4050026012809004201e00e807002e01600a004c0220100078030012008003801800a0040018008002000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xa4143a7f4f89ed3c2754da9a9322614a894126a4b48e9112123b4708d91998a3025e4bb1752e45bcb39642bc56ca714a28e514a093e2784d49913025a4848c11021a430849061fc3ec7a8f21ca3846f0dc1b0354698cc19231c620c11802fc5f0bb1702d0598b1160230358620c217c2f05c0b61682b8540a61481a82c0560a41402604a0901081e03a0700b81602804c0881001e0300480800e0180280400600800800 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x65131dd89ec3c51ea8493d49d74d3a5bd2ce94b4a2a4c1236913486a3fd1ee8f14751aaccfc6553209748a7a52a270134493446722a110c8464112010fc46c62ce15d89c44c422b0fc07943a81b40d1064c3041560a78520282133092845c214104077827812c09204682300f607303781a80d206403101800bc05b02d01600ae05602a815008603b01b80c806202c01500a004c023011008003e01e00e807002e015009804401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x69fb4399c0cca539a929446a104d124311f28ac44d219106081e4069fa4fb07c83db94fca2c4ef26e11b87b03c51bc0d986602fc1750b6456a2a414a0a0c4641fa0f907583a01bb0d3067833018a0c105f02ea1600ac854829613d097848422610c07b827812c09204682300f607303781a80d206403101800bc05b02d01600ae05602a815008603b01b80c806202c01500a004c023011008003e01e00e807002e015009804401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x6b8d39a133c57eac552a9f5149c9372624c095d2724a4909091f23c4726e4d599f332610b61682b8568a89482885089e13826c4cc8d9031fe3cc788e81be36c6c8d319e334650c11802fc5f0bc1742e05b0b51642684908e1122203c8710da1a0338620c01782e0590b01582a8540a61482183b06e0c81882c0540a0130230440800f81e03a0700b8150260440700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x671b1e9834c135b0abd1560a94528292547699e4bc24e522690b47b213107c8304061ff8fe07e738a9a7ccd463e30497f8bf05632a994389fc4f327491bc8b445022010ac84241a17b0bc04ee26412c08f445421e10187e832217e0ba05ac29a14309d049822a10707c03a4128093048023c10407c03881bc0da06b031017c0bc05b02c81540a804a02200e006e03401980a404e025011808003a01c00b004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ac78c76a7636f76ca6a86946706636495ff5ed5c95b55a858354b54553e52f52952251c4a446544d42e40e3f03e438938034d34132330c2dd2d02c92c22b62b02ab1dd1d31a719c19418517716d15f15812711c11410c0f70ed0e60d80cc0c80c40c109209108e08d08207c07106f06d06b06205f05e05b05905505404a04403803703403302902702502302001d01c01601301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x9c53025049c8a70e613c1c80f00dfc3ca77eebdd23a071cd95b0b5a698d19a0b3c5d4b0d5baa4522a1940a4447c89910216416794ed9d539a704de9b829a5209512524246c8990e20a408718dc1ae34c640c41822ec5a0b115c2a8430851042043b8720d019c328640b81682c8570aa144280470840dc1b0330640a4138250460800e81c02c04c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6ce69a65a64d5e65c95a559957356a55550f4f84de4c84bd49c44443942f41440d4063fb3ad38a36c35933a32631c2cd2bf29c28f2782632182001f61e51d41cd1c215f15b13b13512f12812211c1121100f50ed0e70e40d70d10ce0c50bd0b70b40b108608508208107807406a06806606405b05805705405204e04d04704303803703403302902702502302001d01c01601301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0xa01392644c49031a62944885509e103f27cef45dfbba756dddb936c6b2d4da634661ebbd6cacb570ac5572744d295926a42472820fe1f53d8780ed1d42cc58ca313f26e4b09191d222434780e81c036c660c61802d8580ab150290420831001fc3a0710ce198320620b215c2b0530a2134260450820d81a8330640a0130250460800e81c02c04c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame005_links_0000 record020_frame005_links_0064)
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
def record020_frame006_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x75ae79c43816b8d399f33a654c958d2fa5e0b896b2d0580a614a28e50aa093ea7a4bc9191ca2c43e849069ef3d476ceb1ca38467cca99131660cbf97c24447c831001f63d0770e91c4380628bf1742dc560a814a27c4c89512623c3c0770ec1d43606a0c41802f85d0aa1482884e0981202384107e0d01983005e0a0138250460800e81c02c04c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record020_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record020) (record020.maps 6)
      (record020.inverseMaps 6) record020_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame006_links_0000 record020_frame006_links_0064)
theorem record020_frame006_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 6 :=
  of_group record020 6 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record020_frame006_indices record020_frame006_graph record020_frame006_links
def record020_frame007_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7e97bb78c7847126f36db6ce6a469e68c6466316105f15e95c257256c56254853e5325274c848c46b4544364214133c63b93a539b38b37832b31730a2ff2ee2e62dd21f2161db1d21c71b91a91a018b18114613a12e12510c1050fc0eb0e10d90d20ca08e08d08a08907e07806e06c06a06805f05c05b05805605205104804303703603303202902702502302001d01c01601301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record020_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record020_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7)
      (record020.inverseMaps 7) record020_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record020_frame007_links_0000 record020_frame007_links_0064)
theorem record020_frame007_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 7 :=
  of_group record020 7 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record020_frame007_indices record020_frame007_graph record020_frame007_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (Fin.cases (record020_frame006_supported hcells) (Fin.cases (record020_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x15feb6d639a331a5b47588104e054037fcfe1f6be47bcf4dc2b60694d019b32c642bc56b2c857ca8d4aa724c293923a4145688d099f23b6724dd9a13345c0b315c2985189c9282303c4760e11b6354630c01762d8450820fe1f0388690ca18c2e85a0ac1542804f09c1101c83806a0d01902b0540a0130240460840f01d0380580a01302003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x69d6765f05da5bf5b05ad55d54c52451c5114bc4b149e49048547f46b3f93e03c43b33b037035f33d33732f2e22db2ce2c32bc2b62a927826d26424d24622d22421b2172101ed1d11a519117e17416414212d11e1060fe0ee0e00d50c908308107f06c06b06906706405d05b05a05705505105004f04e03a03903703503202b02902802502301f01e01d01c01601501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x67065e5f85da5bd5aa59d55553b51850b4f64b44ae4a249b4954904834223ff3e63d33c837b35c33c33031d2d82d22c62c02bb2b72ae28928027524e24922721d2122061f91d51c419818617216815513e12c1140f60ec0d80c50bc0b808708608306f06e06c06a06706105f05e05b05905505405305203903803603403102b02902802502301f01e01d01c01601501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x14c28d4bc94922e3f4778990e20ec15816f69e93c677cee5d93a6676c8d84afd5eab0d57a9551aa052c2524909011e237458831011f93c0770e19b93606a0cf1842ea564a713b26a494899051ee3746a8c81762d85808910e2143786e0da1ac340620c017c2e85b0ae1582a8540740e41b8350640ac1482804a08c0f81e03a0700b01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36c9a4eb2a56caa254bca4b4c8a55d1f48e645fa0710187e93eb1f1cf6e7952fb1694aaa52a28b91748463c61d90e2c5d02d815a8a8852628313088e446422b10a083c3f41f30f5878c3b81c20da065c31417b0ba859c2a414409a848423210c07f03d81e009504902340e407103781b40d406303081800ba05b02b81580aa05401d00e406e03501900ac052028012808c03e01e00e807002c01500a004c0220100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
def record022_frame005_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x12f2564628990f2184297daf69dfbb6742d85ac34b688cf99d3315f4b85662bd5649dd32a504928e8fe9f53d0780ed9d739c6ecdb9b134a688ca98f31260cbe96c2c050c9b127242458810f51ce348650bd1642a8520831001ec340670ca18c3085a0b015c2a05209c1342604b0700dc1a8330600a81402704a08c0f81e03a0700b01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record022_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record022) (record022.maps 5) (record022.inverseMaps 5) record022_frame005_indices (Fin.ofNat record022.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record022_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record022) (record022.maps 5)
      (record022.inverseMaps 5) record022_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record022_frame005_links_0000 record022_frame005_links_0064)
theorem record022_frame005_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 5 :=
  of_group record022 5 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record022_frame005_indices record022_frame005_graph record022_frame005_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (Fin.cases (record022_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x67eb231530a274d7269d3409894c225bd2d09604ac254522690c47fa3dd1e08ea46e1c2cd2a5e32e91700b0857429e94aca2e503279115088442320890047e23d11ba0d8c6a23151828b385782a814a0a0c3ca1d30da06883241820b1055829e1480a084e822e10407b03bc1d209504902340e406f035018c0c406103001780ba05b02b81580aa05401d00dc06402b01500a4050026012808c03e01e00e807002c01500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6d9349d5b2a5e4db26893229574a324311f48e646922fd03c80c3f49f60f8e7b73ca9694a5448223711748464121ec0f1876439e1c58ba85b02b51520a4c50626111c88c845621410787e83e61eb0f1877033c1970c506082f61750b385802b21520a5851024210c07f03dc1e009504902340e406f035018c0c406103001780ba05b02b81580aa05401d00dc06402b01500a4050026012808c03e01e00e807002c01500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x6f4d596eab951aa2943a7c4f69c937a6b4ce991252474848f91da3946675cd9987308604bb1752d85a4b29612bc510a093c2704d49992d23c46c8c10d21840c800fc1f03d46d8d81a633c660ca188304600bf17c2f45c0b51662c85889111c2243806d0d01843005f0bc1702d8590aa150298520740dc1902b0540a41402604a08c0f81e03a0700b01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa90a4d94690289388687b84e84581c8097f67de7cd73a7267006ec6da6c86a25e059c53e53452a5024fa4da4cc4bc4aa49c4244143f53e53d73c73a837936d36033832d3052f52e62d72cb24823821a2081f91e91cd1c21ba1ae1a019114611c0fe0f30e808f08c08707006d06806106005f05e05c05b05905505405305203a03703202b02a02902802602502301f01e01d01c01601501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x692acfd512a5c525a6452ae8ab42120bd0387fa3f49f58f907b63ca982caaa52828b91748463771870bec5d02c615a8a8852828213088e446422b10a08203f41e30ea87243681ad0d2864031417c0ba059c2a414409a848423211307f03d81d209f04982340f807103801b40d406303081800b805b02c01580aa05402200e407003501900ac052028012008c04001e00e807002c01500a004c02200f0070030016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc8a512a6b934e9a04c4a5f52de9584a52489234913482a3fd1ee8f1474a370d265e32e91700b0856129e940c9be477233115086242320890087e03d11ba0d8c6a23151790b3852827010407dc3ca1c20da06883261810b1055829e1480a084e822e10a07b03bc1c609f04982340f8070035018c0c406103001780b805b02c01580aa05402200e006402b01500a4050026012008c04001e00e807002c01500a004c02200f007002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd2552e26d93449914aba4c92188d2455a10905e81e3fd1fa4fb07c83db1e54a5048223711748463fe1ec0e786ee30e17d8ba858c2b51520a5050426111c88c845621410407e83c61d50d6869433c1900c506082f81740b385802b21520a5851024211307f03dc1d209f04982340f8070035018c0c406103001780b805b02c01580aa05402200e006402b01500a4050026012008c04001e00e807002c01500a004c02200f007002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x355570a35452874f89e1392674c294526a4a4889091f23c4708ccd9187308604bb1722d8584ad94b28e5109f13c2704d89912d23c46c8c10d21240c7c0f21c43786d8d51a633c668c9188304600bf17c2f45c0b61662c85809b11e2243d06e0d01843005f0bc1702d0590ac150298520880e01902b0540a41402604808c1001e03a0700b01502804c0880f01c02c0480800e0180280400600800800 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x693aa254bca494c8a55d1cc8d146022b1134864421202cff27d63e41edcf2855529514548ba4231d90e747183781b30cc061c2d71628a8852828313008e446422b10a07e83d61dd0eb07403921c20dd86d035a19d0cb063c2f81750b30548288135090846422610c07b036c12a08d03d81c80da06a03181840c005b02d01600ae05602a010c07403501900ac052028011808804001f00f007002c01500a004c02200e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6912e6d4409b6472234d1808aa44d22210a4842416a0750167d93e41ed0f28667276120876039f1c60dd86cc35418f0c385f22e916b8a9452828013008e446422b10a07903ba1d00e487083761b40d6867432c18f0c185f02cc1600a58510278127090846822610b074036c16608d03e01e40e406b03501880c205b02d01640b005602a011008203a01980c8054029011808804202000f007002c01500a004c01e00e006803001600a004801c00c0050018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa4a99e8d28937f47df7ce7bc7a879b76f76074d7397256ed6db6c56a163956c53e4ba4ab49d48d4804754524444334234133e63d83c43a737936d3603382d82cc2ac2a02962862752672472372262091fa1cc1c21a019118215514613712b11b0da0c00a108707a07707006906806005f05905805705605405204404103a03303202a02902302202102001e01c01601501401300f00e00d00c00b00a009007006005003002001000 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x325191aab7554a4ed25491b48522210ee86842ba0f506c82f3c69b8ccb065132515b0aa251528513f09be4c424411f48de46522d91588a234f1980c2c5dc2dd1570a3c4d424d11e08a844621c10a862c2f616a0ab851427610807f034813e09e04a82500f807a03901c00c605c02d81680ae05602a811008604201d00e407002b0150098048023011008403e01e00e8058028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x15aeb04c496713222c4287702a01bff7f0f75ebbd175ee159a32963cb215f29b52ea3540a7249c92120a35444865089c937669cce1922fe5c0ae14d28c4c49391e22c3c4760e71c236c6a8c017629845089106208388700d41a42e8560aa1502885009e110218420740e41c02b054098120230440840f81e03a0580a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record028_frame002_links_0000 record028_frame002_links_0064)
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
def record028_frame003_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x125a47c2282ced5d6ba873edc9b5b646b6d21a2340656c0564ac357c9d93625249c9111b22c41c81cfd9f33d278cee1953125e0b595f2a05189b12b2424508810a2063746b0d1196320618ab154248418820fa1f03706c0ce1982d0530a41442704d0981001f83e0700dc1b02a052094118220420800f01d0380580a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record028_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record028_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record028) (record028.maps 3)
      (record028.inverseMaps 3) record028_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record028_frame003_links_0000 record028_frame003_links_0064)
theorem record028_frame003_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 3 :=
  of_group record028 3 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record028_frame003_indices record028_frame003_graph record028_frame003_links
def record028_frame004_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x66f66a5bd5b251a50f5095004c24b74b24a949348f48b4463f73ac3a73a13313213002fd2f62e22d82b12ad2a72a029629329021e20d1fb1e81e01c41b91a419018a17b17417016c12811f11610b0fe0f60d40cc0ae09309208d08c07807607006e06105a05905805505405304304204103a03903802b02a02602402302202101f01e01d01601401000f00e00d00b00a009008004003002001000 } : Fields).get c.val)
theorem record028_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record028_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record028) (record028.maps 4)
      (record028.inverseMaps 4) record028_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record028_frame004_links_0000 record028_frame004_links_0064)
theorem record028_frame004_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 4 :=
  of_group record028 4 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record028_frame004_indices record028_frame004_graph record028_frame004_links
def record028_frame005_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0xd85acb0f606b11602bd56ea4545a885049b93426349e8cd032003f471cdd9a934c67ccc98f2f05dcb916a2c4578ad12e24c4708890c1fa3d4750e31bc348670ca18e2ac540a71482784d08d1142003a0730de1b8330650c21802b85009e1382584a092110218420740e41c02b054098120230440840f81e03a0580a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record028_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record028_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record028) (record028.maps 5)
      (record028.inverseMaps 5) record028_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record028_frame005_links_0000 record028_frame005_links_0064)
theorem record028_frame005_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 5 :=
  of_group record028 5 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record028_frame005_indices record028_frame005_graph record028_frame005_links
def record028_frame006_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0xff5fb38c702ce59ab3265ac3183b045fcbb5732e3582a452724948881cfe1e73ca77ce99c93626b4d39a132e648c79522944f49892b23c468861001f43c4750e51c6310608bf1782e0598a51462543d0790ec1d4348670c61882d8540a61482784e09a0f81e83c06c0d41a0290500901102104007c0e81c0360580a01001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record028_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record028_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record028) (record028.maps 6)
      (record028.inverseMaps 6) record028_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record028_frame006_links_0000 record028_frame006_links_0064)
theorem record028_frame006_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 6 :=
  of_group record028 6 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record028_frame006_indices record028_frame006_graph record028_frame006_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (Fin.cases (record028_frame003_supported hcells) (Fin.cases (record028_frame004_supported hcells) (Fin.cases (record028_frame005_supported hcells) (Fin.cases (record028_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x6832df1538a8853c299942093048e24311f48ca461a2f11328924459c9ccbc64b31c98a0ba450927b13909a64a424e92588ea46f234900c6062ef16d0b1c5722a914c8a284f423c116887441c1d60e306d834e1970ac852827412b07b83c01d20e206d835016609f03e01c80e207003581a80d206303101840b805b02d011007403901c00cc06403101580a8052024011808802c01500a003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78c76a6f76a86896706495ed5be5b558355254d54553e53652952251c4a446f44d44343842e40e4013e439338037635734d34133430c3062d82d02c92b62b02ab22420c1dd1d31bc1a719e19718517915f15812e12711e11710c0f90e60d80cd0c40c109208e08d08207c06f06c06b05f05d05b05805505404a04403903703503403302a02702602502302102001d01c01601301201000f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b5ead6562a9251a28c145622650c88423fc9f9cfac7b73d39e50b4459128a8e7471a3781b28cc061c2c51598a8850627313008c844820f0ef075839e1c90e106ec3681ad0ce863c3101750b705982a414409a84bc23210c08283d81b60a504a823c10407b03901b40d8063030017c0ba05a02c015c0ac054025010c07403501a00ac050027012808804001f00f007002c0150098048022010006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x186caa554c292522c901474a34d13c87b419207500c7de3e41ec0d626a43279554a8a53529393e49b64a024912048c24522208fc07a83ad19e8ca062c30617a0b8c5a62c215309fc4da236112083c3c01c30d506602ca14209904401b00a504a823c10407b03901b40d8063030017c0ba05a02c015c0ac054025010c07403501a00ac050027012808804001f00f007002c0150098048022010006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xb9d6dace58daeb5a6955149e338a644c28e91a22dc5186d0a610be478cea9ce3826e8d0998318618be97baba562aa55028e50c9f92aa47442844f99ed3d077cea1b3340634c11662ba5609d12f244448840f61c834c5a8a91082043b0720d21a0330650b81682c8570aa1502885008e1081b8360680cc1502704a08c1082003a0700b0150260480800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
def record032_frame002_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x6f76ca6a86896706495ff5ed5be5b558357b54d54553e53852952251c4a446f44d42e40e3e439338034d34130c3062d82d02c92c42b62b02ab27225b22420c1dd1d31cb1c31bc1a719718517c15f15814b13512e12711710c0fc0e60d80c40c109208d08207c07106f06c06b06205f05d05b05905805505404a04403903703403302a02702502302102001d01c01601501301201000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record032_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record032_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record032) (record032.maps 2)
      (record032.inverseMaps 2) record032_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record032_frame002_links_0000 record032_frame002_links_0064)
theorem record032_frame002_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 2 :=
  of_group record032 2 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record032_frame002_indices record032_frame002_graph record032_frame002_links
def record032_frame003_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x9a72f251c928fb1ba22c3783b052013fe7a6f35e2bbf760eadd3357676c8988afb5d6af9572955169e13a25349a91d212354628b1011f23966e4ca98e314610be1662b4534a212b24a480861051f83bc720d618e2ec548a21102183e8780dc1b4350690c21782e85b0b21602a8540941101c8370680cc1502704a08c1082003a0700b0150260480800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record032_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record032_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record032) (record032.maps 3)
      (record032.inverseMaps 3) record032_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record032_frame003_links_0000 record032_frame003_links_0064)
theorem record032_frame003_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 3 :=
  of_group record032 3 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record032_frame003_indices record032_frame003_graph record032_frame003_links
def record032_frame004_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5cc2ca95aea9d52da8892fc95647d23911308884069fe0fd07d93da1e98f2a6642fb168cad252727711288443c61d80d906a82d91620ad054a280139098446422410087cc3aa1ce0e487083761a40cc062430616d0b3858029614409e04bc24e11a08583f81d00e204a023c10407c03881bc0d806b031017c0ba05b02c81600aa054025011007203701a00cc054027012808c04202000e807002c015009804802000f007003001600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record032_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record032_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 4)
      (record032.inverseMaps 4) record032_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record032_frame004_links_0000 record032_frame004_links_0064)
theorem record032_frame004_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 4 :=
  of_group record032 4 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record032_frame004_indices record032_frame004_graph record032_frame004_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (Fin.cases (record032_frame002_supported hcells) (Fin.cases (record032_frame003_supported hcells) (Fin.cases (record032_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x36a56889a74cca5d92d094a4a1a4f921a90547f23e11d28e246e1f28ba45ac2a794ac9be4cf25f110c8624222090fc07c03d11b18cf45c02bc138098049e1d40e106cc3461810b885882ac14f0a4050427412508803d81c60dd052827c12808f04101f00e206c03181880c005f02e81700b605902c01540a804a02200e406802b01500a004e025012008c04202000e807002c015009804802000f0070030016008003801800a0040018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a257309a24bf24791f48ab44c222101a7fa3f41f64f6c7a63ca99908dc44a1f50f186ee3641aa0b6458c2b41528a084e426111908904021f30ea87383921980c806243061740b6859c2c01590a9052c28812f08d03f81d20e2052827c12808f04101f00e206c03181880c005f02e81700b605902c01540a804a02200e406802b01500a004e025012008c04202000e807002c015009804802000f0070030016008003801800a0040018008002000 } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xea185a8a5089d537a614bc975242444828fd1c235466814c217e2de5a4ad9582ae5089f13b2724c89792d236454831001e43bc770d91aa348680c918c310608c017e2f85e8ba16e2cc580af14226c4808b1001e83786a0c21802f05d0b61682c8570ac14c2904a0880e41a02b0540a01382504808c1082003a0700b0150260480800f01c0300580800e0180280400600800800 } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
def record033_frame004_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x1966e7538a5540a78ccf99130a3a46a8b71461c429842f91a5342644c617fafa5eeae959aa9540a414327e4aa91d10a113e67b4f41a0330634c11712cc574ac15028a4e8979121ec34c5b0a9116224420810ec1c8348660ba1702d85a0b21602b8550a8144280470840dc1a02b0540a01382504808c1082003a0700b0150260480800f01c0300580800e0180280400600800800 } : Fields).get c.val)
theorem record033_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record033_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record033) (record033.maps 4)
      (record033.inverseMaps 4) record033_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record033_frame004_links_0000 record033_frame004_links_0064)
theorem record033_frame004_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 4 :=
  of_group record033 4 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record033_frame004_indices record033_frame004_graph record033_frame004_links
def record033_frame005_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x12120fbb8760e59c63766e4db9a3b4066ecc190b18624b9536a6749a8fd15a264467e0f99eb3c6758e59c434e670c197b2d2590b093325a4888d1102104087e8fa1ec3c0748db1962dc540a31162204087d0e81c4350660ba1702d85a0b21602b8550a8144280480880e41a02b0540a01382504808c1082003a0700b0150260480800f01c0300580800e0180280400600800800 } : Fields).get c.val)
theorem record033_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record033_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record033) (record033.maps 5)
      (record033.inverseMaps 5) record033_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record033_frame005_links_0000 record033_frame005_links_0064)
theorem record033_frame005_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 5 :=
  of_group record033 5 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record033_frame005_indices record033_frame005_graph record033_frame005_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (Fin.cases (record033_frame004_supported hcells) (Fin.cases (record033_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5ccab5953aa5d51025f92ac8d3460a2a9132888429210905a81d3f39f64f687a73ca1994b4456929493b08944221cf8e346ec3651aa0c7861c2f91748acc54a280139898046422410087a83c81de0e787243841bb0da06b433a18f0c4060c2dc1660b0052c28813c097849c23410b08283a01b608f04101e40e406c03581880be05d02d01640b005602a012808203a01a00cc054027012808804202000f007002c015009804802000f006803001600a004801c00c0050018008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xc8d5c32b9156eaa24b2254127692d48c242916289d44421e90ca85742220d905e77d3979b4cd0a658328990caf25512a194c8a3050727e13b09884b6252922c8f446f23291808ac4511be0d3c66030b17f0b7455c28f135097447822a111887042a1b70d0862c2f81690ab8514260108079834813c09403e01e40e406f02e816c0b405802b015408804302080e8072037015009804a023011008404001e00e8058026010007803801a00b00500240100050018008002000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x16d2b205622abd538a8953ba9993fa9b44ac250d26091d485a3e91948c345aa28112488b38b1b54d0267132f1930c706282e09600a5851c28493dc9c64d3252127491e47b23791a47d43911960c606062f016c8b1c5722a914c8a284f424c11688744001d60e306d834e1970b4852827411d07b83c01d20e206d83500e407103781b00d406903181880c005d02d816807403901b80d006403101580a8050025011808802c015009804001c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe1e6aab2f18feb825702a6d354940496a45920e8f7446a1e90c6854425a11105e65832198f4b0a5792b6157ca6252628c13e49d84df269129093248b23611948c045b2288dec6da33f1980c7061c2fe1758b3053c28f13d89b44ba24a11888a843821510306382f81670ab04b82480f107383481840b904e02480f006e02f01740b405902c0154094044020810007403701b00a004c025012008804202000f8074024011008003801a00c00580240100060028008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
def record037_frame002_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x6a6cf995b1d5f2b77646a0d049f33a66e4d59372463ec708d1192293b5752e8dabb5469ad119331e62abf97c2f35d8b2961abc544a6d4c2955168d51821b424810fe9f23d2760e19bc358694cf1912fc5e8b79692c64948d1091f83846c8b515a26c4908e1041f0348620a814c2804f09c12c2203f07a0f01b8350680a0130250480881082003e074090110200380680c0160240400600a00800800 } : Fields).get c.val)
theorem record037_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record037_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record037) (record037.maps 2)
      (record037.inverseMaps 2) record037_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record037_frame002_links_0000 record037_frame002_links_0064)
theorem record037_frame002_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 2 :=
  of_group record037 2 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record037_frame002_indices record037_frame002_graph record037_frame002_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (Fin.cases (record037_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78c6f76a869f6946896706495ed5e45c95be5b558357b55454d54553e52952251c4a444d44343842e40e3e438037635734d34130c3062df2d82d02c92b62b02ab23c23222421a20c1dd1d31cb1c31bc1a71a119718515f15814b13512e12712111710c0e60d80c40c108e08d08207c06f06d06c06b05f05e05d05b05905805505404a04403703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
def record038_frame002_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6925f95b65b25ab5a459358453a5305135094fd4e14d94a649c49048a47747146c3f83ac3a83a339e38e38033132b31430c3032ec2e72bd2b52ac2a829a29729422421920c2031fc1da1d51cc1c11b419c19618f17d16616215913d13212611e1131070e60dc0c00ba08a08907c07606d06b06a06905d05c05b05905705605305204804203703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record038_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record038) (record038.maps 2)
      (record038.inverseMaps 2) record038_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame002_links_0000 record038_frame002_links_0064)
theorem record038_frame002_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 2 :=
  of_group record038 2 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record038_frame002_indices record038_frame002_graph record038_frame002_links
def record038_frame003_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0927.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0927.count (({ width := 9, code := 0x279268fc7a391b8c45a1d0d854260f0481bf9fafb7d3e1eef674b89c2df6f36db2d16833598ca63b1982c05f2f574b95c27d3a9a4ba511e8d452210a82401f4f072381b4d6683298cc05d2b14c9c4c2110474391c0dc6c351a0cc6431180bc5c2d13094482311084401f0f074381b0d0642610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record038_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record038) (record038.maps 3)
      (record038.inverseMaps 3) record038_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame003_links_0000 record038_frame003_links_0064)
theorem record038_frame003_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 3 :=
  of_group record038 3 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0927
    Papers.RationalityTen.SharedFrameCatalogue.group0927_facts record038_frame003_indices record038_frame003_graph record038_frame003_links
def record038_frame004_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0948.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0948.count (({ width := 9, code := 0x267208cc622d158944211078240e02fe7ebe1eef57a3c9e2f07337dbcdc6db61acce66b2992c76230d7cbd5dae96eb65aa7d3a9a4ba511e8d452210a82401f4f072381b4d6683298cc05d2b14c9c4c2110474391c0dc6c351a0cc6431180bc5c2d13094482311084401f0f074381b0d0642610078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record038_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record038) (record038.maps 4) (record038.inverseMaps 4) record038_frame004_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record038) (record038.maps 4) (record038.inverseMaps 4) record038_frame004_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record038) (record038.maps 4)
      (record038.inverseMaps 4) record038_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame004_links_0000 record038_frame004_links_0064)
theorem record038_frame004_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 4 :=
  of_group record038 4 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0948
    Papers.RationalityTen.SharedFrameCatalogue.group0948_facts record038_frame004_indices record038_frame004_graph record038_frame004_links
def record038_frame005_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8699c94493d9329299018d484d84581c8097f47a679b73b7277106ff6c56b46a26375de5d85cf5c659a56e5014fa4da4cc4ba47e4754254154013f43c43b73a832d3203133052f52bc2aa2a02962862582492392191da1cd1c21a019118217316515511b0fe0da0ce08a08907e07a06d06b06a06905d05c05b05905705605305204a04403703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record038_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record038) (record038.maps 5) (record038.inverseMaps 5) record038_frame005_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record038) (record038.maps 5) (record038.inverseMaps 5) record038_frame005_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record038) (record038.maps 5)
      (record038.inverseMaps 5) record038_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame005_links_0000 record038_frame005_links_0064)
theorem record038_frame005_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 5 :=
  of_group record038 5 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record038_frame005_indices record038_frame005_graph record038_frame005_links
def record038_frame006_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x207bd3762eb5d339d71ede5a734a676cd19630f614bcd762e65c2b4165ac75289bd35a654ba9391d20c4107e0f91eb3a072cda1ae35068cc998f31657cac1512945049592824c4908f11222042c800e61c4378698d1194324618bc14a268468890e01bc350680bc1742e05b0a61482884f09a130248480840f0190310600bc1382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record038_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record038) (record038.maps 6) (record038.inverseMaps 6) record038_frame006_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record038) (record038.maps 6) (record038.inverseMaps 6) record038_frame006_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record038) (record038.maps 6)
      (record038.inverseMaps 6) record038_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame006_links_0000 record038_frame006_links_0064)
theorem record038_frame006_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 6 :=
  of_group record038 6 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record038_frame006_indices record038_frame006_graph record038_frame006_links
def record038_frame007_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x2143e078cf0de03bd760e89bb3726c0d65a9b3a66cc4d86b045fcbb9742e2566a554928f5169f938a4748a8d518a2c432860fd1f63e07b0f01dd3b465cc898930e608b49642c2574ab94127c4ec9711b22c4447c8f31d63986f8d617e2d05089a1001fc3a0710d219c330650b61682c8570aa1502885008c1041b8350680cc1382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record038_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record038) (record038.maps 7) (record038.inverseMaps 7) record038_frame007_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record038) (record038.maps 7) (record038.inverseMaps 7) record038_frame007_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record038) (record038.maps 7)
      (record038.inverseMaps 7) record038_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame007_links_0000 record038_frame007_links_0064)
theorem record038_frame007_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 7 :=
  of_group record038 7 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record038_frame007_indices record038_frame007_graph record038_frame007_links
def record038_frame008_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b3ab9856bab15562a9d52da8892ac94648623e91c8898444207d01a7f83f41ed0f4c795332168cb2257d2b4949c9dc4222090f6078c3b01b20d505d62d91620ad0500272130883c4102010fd07cc3aa1ce0e487083761a40cf866031216d0b3858029614409e04d825e12708583f81d00e2048023c10407c03781b40d806b02f81780ba05b02c81600aa054025011006e03501a00cc04e026012808c04202000e807002c013009004402000f007003001600a004001c00c0050018008002000 } : Fields).get c.val)
theorem record038_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 8) (record038.inverseMaps 8) record038_frame008_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 8) (record038.inverseMaps 8) record038_frame008_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 8)
      (record038.inverseMaps 8) record038_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame008_links_0000 record038_frame008_links_0064)
theorem record038_frame008_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 8 :=
  of_group record038 8 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame008_indices record038_frame008_graph record038_frame008_links
def record038_frame009_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x25945b8590a21241f820ff5dfbba756e91cf37c6ecd4da5b43676cad92b1e5daae159aaf550a5d3f2444808cd1722841a820f29dd3a8734de1b636060cbf1782e45b0ae1572a6534a413926c4c09090c20c400790ed1cc38c6e8d517c2cc538a10f41e43706a0c01782e85c0a814c2905009c134250490820f41a0320620c01382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record038_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record038) (record038.maps 9) (record038.inverseMaps 9) record038_frame009_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record038) (record038.maps 9) (record038.inverseMaps 9) record038_frame009_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record038) (record038.maps 9)
      (record038.inverseMaps 9) record038_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame009_links_0000 record038_frame009_links_0064)
theorem record038_frame009_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 9 :=
  of_group record038 9 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record038_frame009_indices record038_frame009_graph record038_frame009_links
def record038_frame010_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1040.count (({ width := 11, code := 0x201bb171ae29c3b826eada19db37658ca591b14622be179aeb5ceb5d6a2d05289d138a6e4d296927a2243c845062043e87c4ed1d73a2738df1ba36e5ecba96f2d0590a61482864f49b92824647c881021fc3e8768e51bc368690cb16a2b84d8980fc1f43806c0ca18c310610ac1542a0520a013c2604b0820f41b0340660c81382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record038_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record038) (record038.maps 10) (record038.inverseMaps 10) record038_frame010_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record038) (record038.maps 10) (record038.inverseMaps 10) record038_frame010_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record038) (record038.maps 10)
      (record038.inverseMaps 10) record038_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame010_links_0000 record038_frame010_links_0064)
theorem record038_frame010_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 10 :=
  of_group record038 10 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1040
    Papers.RationalityTen.SharedFrameCatalogue.group1040_facts record038_frame010_indices record038_frame010_graph record038_frame010_links
def record038_frame011_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0910.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0910.count (({ width := 8, code := 0xc3bcb8b7b6b5b4b3aeadacabaaa8a7a5a4a3a2a1a09f9b9796959493928d8c8b8a89878684838281807f7e7573716f6d6a68666462605e5c595553514f4d4b494745413e3b393534302f2e2d2c2b2a292827262524231f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record038_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0910.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record038) (record038.maps 11) (record038.inverseMaps 11) record038_frame011_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record038) (record038.maps 11) (record038.inverseMaps 11) record038_frame011_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record038) (record038.maps 11)
      (record038.inverseMaps 11) record038_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame011_links_0000 record038_frame011_links_0064)
theorem record038_frame011_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 11 :=
  of_group record038 11 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0910
    Papers.RationalityTen.SharedFrameCatalogue.group0910_facts record038_frame011_indices record038_frame011_graph record038_frame011_links
def record038_frame012_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x69a5e65a55a059958e5735554f84f24de4d24c849c49545944a43942f40d4063fb3ad36c36735e35933a31c2bf2b92a229c28f26325c21e2112001f61d41cd1c218b18718117c17715f15b15715414f13b13813212811211010c1000fb0f50f00ea0e40ce0c50b40b108208107807406806606506405805705605405205104e04d04704303703503403302702602502302102001d01c01601301201101000f00e00c00b00a008007006005003002001000 } : Fields).get c.val)
theorem record038_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record038) (record038.maps 12) (record038.inverseMaps 12) record038_frame012_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record038) (record038.maps 12) (record038.inverseMaps 12) record038_frame012_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record038) (record038.maps 12)
      (record038.inverseMaps 12) record038_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame012_links_0000 record038_frame012_links_0064)
theorem record038_frame012_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 12 :=
  of_group record038 12 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record038_frame012_indices record038_frame012_graph record038_frame012_links
def record038_frame013_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x1cf35c67ccf59d335654c69782ef5c4b716b2c0576a854da9451ca093ea7a4bc8e51c23245887d069ea3d2774ed9d63846f4d119d32a644c197f2f8524a293f2764d89111f23a4688a9062063f87a0e21c0370670ca18a3085e8b714a27c4988f0ec1d43606a0c017c2f05d0a41442804e09812c240470820fc198310600bc1382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record038_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record038) (record038.maps 13) (record038.inverseMaps 13) record038_frame013_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record038) (record038.maps 13) (record038.inverseMaps 13) record038_frame013_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record038) (record038.maps 13)
      (record038.inverseMaps 13) record038_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame013_links_0000 record038_frame013_links_0064)
theorem record038_frame013_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 13 :=
  of_group record038 13 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record038_frame013_indices record038_frame013_graph record038_frame013_links
def record038_frame014_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x2053b672ce49c73886f6db5a134166ccc59631962cbe97aaed5d2b6d6aad053ea114027b4f09a52da3045c8790ca144007f8f21e23b475ce49c237c61cc097d2f25c8ac95329c530a293025c4ac8d9041fa3dc738e21ba3686a0ce1782c05009a0f41e43706b0c41802f85e0a814c2905009c134250490820f41a8330640c41382604a08c1082003a0700b0130240440800f01c0300580a01001c0300500600800800 } : Fields).get c.val)
theorem record038_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record038) (record038.maps 14) (record038.inverseMaps 14) record038_frame014_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record038) (record038.maps 14) (record038.inverseMaps 14) record038_frame014_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record038) (record038.maps 14)
      (record038.inverseMaps 14) record038_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame014_links_0000 record038_frame014_links_0064)
theorem record038_frame014_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 14 :=
  of_group record038 14 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record038_frame014_indices record038_frame014_graph record038_frame014_links
def record038_frame015_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0503.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0503.count (({ width := 8, code := 0x7e7a7978777675747271706f6e6c6b696867666564636261605f5e5d5c5a59585756545351504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record038_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0503.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record038) (record038.maps 15) (record038.inverseMaps 15) record038_frame015_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record038) (record038.maps 15) (record038.inverseMaps 15) record038_frame015_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0503.localPairCheck (smallEmbedding record038) (record038.maps 15)
      (record038.inverseMaps 15) record038_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame015_links_0000 record038_frame015_links_0064)
theorem record038_frame015_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 15 :=
  of_group record038 15 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0503
    Papers.RationalityTen.SharedFrameCatalogue.group0503_facts record038_frame015_indices record038_frame015_graph record038_frame015_links
def record038_frame016_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0511.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0511.count (({ width := 8, code := 0x7e7a7978777675747271706f6e6c6b696867666564636261605f5e5d5c5a59585756545351504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record038_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0511.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record038) (record038.maps 16) (record038.inverseMaps 16) record038_frame016_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record038) (record038.maps 16) (record038.inverseMaps 16) record038_frame016_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0511.localPairCheck (smallEmbedding record038) (record038.maps 16)
      (record038.inverseMaps 16) record038_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame016_links_0000 record038_frame016_links_0064)
theorem record038_frame016_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 16 :=
  of_group record038 16 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0511
    Papers.RationalityTen.SharedFrameCatalogue.group0511_facts record038_frame016_indices record038_frame016_graph record038_frame016_links
def record038_frame017_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0498.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0498.count (({ width := 8, code := 0x7e7a7978777675747271706f6e6c6b696867666564636261605f5e5d5c5a59585756545351504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record038_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0498.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record038) (record038.maps 17) (record038.inverseMaps 17) record038_frame017_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record038) (record038.maps 17) (record038.inverseMaps 17) record038_frame017_indices (Fin.ofNat record038.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record038_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0498.localPairCheck (smallEmbedding record038) (record038.maps 17)
      (record038.inverseMaps 17) record038_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record038_frame017_links_0000 record038_frame017_links_0064)
theorem record038_frame017_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 17 :=
  of_group record038 17 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0498
    Papers.RationalityTen.SharedFrameCatalogue.group0498_facts record038_frame017_indices record038_frame017_graph record038_frame017_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (Fin.cases (record038_frame002_supported hcells) (Fin.cases (record038_frame003_supported hcells) (Fin.cases (record038_frame004_supported hcells) (Fin.cases (record038_frame005_supported hcells) (Fin.cases (record038_frame006_supported hcells) (Fin.cases (record038_frame007_supported hcells) (Fin.cases (record038_frame008_supported hcells) (Fin.cases (record038_frame009_supported hcells) (Fin.cases (record038_frame010_supported hcells) (Fin.cases (record038_frame011_supported hcells) (Fin.cases (record038_frame012_supported hcells) (Fin.cases (record038_frame013_supported hcells) (Fin.cases (record038_frame014_supported hcells) (Fin.cases (record038_frame015_supported hcells) (Fin.cases (record038_frame016_supported hcells) (Fin.cases (record038_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcfc6762a5d50e9844bea5d92be94a49f24a524491a48a243520a8e9471a370e146f92ba1584a9e51626f92f891047723311548864311f80f847a23051790b8054e27012788644101f70f307503841810b905882ac14f0a4050427412c09283f41ec0e3052824412008f04101b80da06c03181800be05e02e81700b205802b01540a804a01b00d406802b014009c04c025012008404001e00e807002c013009004402000f006002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdb16ceab6158a94649924791ca8ab444214908482f40fa034ff47b63d39e54b485912090ff87d43b11bb8d5063c30e17d8bac5b22c614109cc4c220f10408043d41d50e486d035a1a50cf86603201740b7059c2c01590a9052c28813609784141fc0e9052824412008f04101b80da06c03181800be05e02e81700b205802b01540a804a01b00d406802b014009c04c025012008404001e00e807002c013009004402000f006002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3796eab716c27b4f09d5352614ba95128a4d4969212223846c8cceb1d22ea5c8b79642b655ca714b28e514a113e2644c09690c2124187d8f21dc394710de1b83646a8c918e310608c017e2f85e8bb1742d0598b01422344608b1001b03586a0c21782e85c0b61682b8560a814c2904a06c0d41a02b05009c130250480841001e03a0700b0130240440800f01802c0480800e0180280400600800800 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
def record039_frame004_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8fa8694593d84583782a7f57bd79b76f76074f73b7277126c76b56a25df5d84fa4ef4e44bb48e4754524444354254154033c63b83a832d3203132e52bc2a02752672592492392271e81db1cd1c21ba1ae1a019117316510b0fe0db09b08b08a08907e06c06b06a06105e05d05c05b05a05705605405305204a03603503402b02802702602502402102001e01d01c01601301201101000f00c00b009008007006005004003002001000 } : Fields).get c.val)
theorem record039_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record039_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record039) (record039.maps 4)
      (record039.inverseMaps 4) record039_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record039_frame004_links_0000 record039_frame004_links_0064)
theorem record039_frame004_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 4 :=
  of_group record039 4 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record039_frame004_indices record039_frame004_graph record039_frame004_links
def record039_frame005_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbf65f3296549492f48c23fd18a88e43aa0c904080e3ff1fb0fb47913bf9db4ca464429d949ca244e525d12948e246422b112487842e1fb0fa47ba35019d0c905ea2c815889e04da25f129091c4722000fa079c3ac1c60da86a03381850bc84902300eb052824412008f04101b80da06c03181800be05e02e81700b205802b01540a804a01b00d406802b014009c04c025012008404001e00e807002c013009004402000f006002c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record039_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record039_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record039) (record039.maps 5)
      (record039.inverseMaps 5) record039_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record039_frame005_links_0000 record039_frame005_links_0064)
theorem record039_frame005_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 5 :=
  of_group record039 5 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record039_frame005_indices record039_frame005_graph record039_frame005_links
def record039_frame006_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0603.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0603.count (({ width := 9, code := 0x10a84bf9faed763adcee370b79b8da6cb61aad06733190c75bad96ab156aad50a65228d449f4d2612c8d4622d0e83409f8f87a3c9e0ea70371b0d4693419ccc6431974b8592b154a85327134984b21904803f1f0f474391b8d86a33190c460281309448231107c3c1c0d8682a1309044200f0602c1208038180a04018080200 } : Fields).get c.val)
theorem record039_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0603.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0603.localPairCheck (smallEmbedding record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0603.localPairCheck (smallEmbedding record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record039_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0603.localPairCheck (smallEmbedding record039) (record039.maps 6)
      (record039.inverseMaps 6) record039_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record039_frame006_links_0000 record039_frame006_links_0064)
theorem record039_frame006_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 6 :=
  of_group record039 6 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0603
    Papers.RationalityTen.SharedFrameCatalogue.group0603_facts record039_frame006_indices record039_frame006_graph record039_frame006_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (Fin.cases (record039_frame004_supported hcells) (Fin.cases (record039_frame005_supported hcells) (Fin.cases (record039_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2e195c8ab755126a92ec9644a8250125a91848523dd1868b144ea2350f486542ba12d0888364179cbcd0a65832195e4aa25432991498a3050727e13b09884b6252926491647a23791948c04562288df06da35f1a78cfc66030e17f0b745982be1570a7851e26d12e88f046222a111887042a2060e606dc34218e0be05a42ae13007983480f807903901bc0bc05d02d81680b205802b015408804101d00dc04c025011808804202000f007402c013008804001e00e006803001600a004802000c0050018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e6d5b2a5a50fa5192188fa47223511828aa44d22210a4842416a07d01a7f83f49f5cf8c7a53c9999cb4a52627590487b03c61d80e8071a3761b30d5063c30e17c8bac5b22c415a8a8c52427112f885041e20810087e83e61e50ef07403921c20dd86d035a19f0cc062830217a0b985b02ca1600a58510278136097849c24210b07403540f807903901bc0bc05d02d81680b205802b015408804101d00dc04c025011808804202000f007402c013008804001e00e006803001600a004802000c0050018008002000 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame002_links_0000 record040_frame002_links_0064)
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
def record040_frame003_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x184ee45a8b27492844ff9ed3b271cd79a331253c9d929226404738d91862d450894f89ccb796c8bd56c2ce58aae958aa453aa3d39a6a4c295d272424788c915a21436784ee1d539c718e01b035266cc918b3085f0bb1662be544a51462844f89d13524a4788b912218418810ea1862b83c8760e01b42e05b0b21602b8560a814c218400740dc130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record040_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record040) (record040.maps 3)
      (record040.inverseMaps 3) record040_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame003_links_0000 record040_frame003_links_0064)
theorem record040_frame003_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 3 :=
  of_group record040 3 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record040_frame003_indices record040_frame003_graph record040_frame003_links
def record040_frame004_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2af94b49ea4dd24bd1d88db46222d514888d442a1d50648204069ff8fd87d93e91ef8f5277d3b59b00ca65e72dd14eca044f4272135c9924b925912948e246422a112487842c213105c80e3e71ed8d846a033a1920c5460c2e816c8afc56229d14509e04da25212388c44442110ff87c83ca1d60d4067031e1850bc85b02c813007503200f807903901bc0bc05d02d81680b205802b015408804101d00dc04c025011808804202000f007402c013008804001e00e006803001600a004802000c0050018008002000 } : Fields).get c.val)
theorem record040_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record040) (record040.maps 4) (record040.inverseMaps 4) record040_frame004_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record040) (record040.maps 4) (record040.inverseMaps 4) record040_frame004_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record040) (record040.maps 4)
      (record040.inverseMaps 4) record040_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame004_links_0000 record040_frame004_links_0064)
theorem record040_frame004_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 4 :=
  of_group record040 4 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record040_frame004_indices record040_frame004_graph record040_frame004_links
def record040_frame005_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x17d2deda3b2f5069351aa1f4127cceb9bf3565dcb394726e48c7f8e71a2324598a5021e83b5752d519f33464ec798ab09602be1712db596b0d5e2ad54aa6d4c2905168d91822844086d091fd3e477cec1d239670cde1a533c61cbf17a2ec5bcb496328e4f09812523442c7e8e316e26c3606a0ca18c2a0530a21402784e09812c1f83d06e0d4130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record040_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record040) (record040.maps 5) (record040.inverseMaps 5) record040_frame005_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record040) (record040.maps 5) (record040.inverseMaps 5) record040_frame005_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record040) (record040.maps 5)
      (record040.inverseMaps 5) record040_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame005_links_0000 record040_frame005_links_0064)
theorem record040_frame005_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 5 :=
  of_group record040 5 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record040_frame005_indices record040_frame005_graph record040_frame005_links
def record040_frame006_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0xfe1e5bb374edc5b235b6aad3da3b3f674ccd9131c626c3982afa5eabb5742e05baaa94126a4bc89d0b20f40e7fcfc1ee3d278ce99d138e700dd9b135868ccf997328594b115d2b2550a814527c4d09812d24e48c8e91321a4087e0f71ea3cc788ed1be36c6b8d219630c5f8b01362483606a0c81842905109e1382684c0941241f03b06e0d4130250460881082003c0740b0130220400780e01a0300580a0120200300500600800800 } : Fields).get c.val)
theorem record040_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record040) (record040.maps 6) (record040.inverseMaps 6) record040_frame006_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record040) (record040.maps 6) (record040.inverseMaps 6) record040_frame006_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record040) (record040.maps 6)
      (record040.inverseMaps 6) record040_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame006_links_0000 record040_frame006_links_0064)
theorem record040_frame006_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 6 :=
  of_group record040 6 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record040_frame006_indices record040_frame006_graph record040_frame006_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (Fin.cases (record040_frame003_supported hcells) (Fin.cases (record040_frame004_supported hcells) (Fin.cases (record040_frame005_supported hcells) (Fin.cases (record040_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x19faa984c4a6112de9684b025692a694b4a2a4f926e930494a48922890d47fa3d91de8e146d1c2cb0857429e94aca2e50527a13809a24be256126891047722a910c8464102000f7c79e3151828b385782a814b0a144e226212788f445621910407983a81b40d086442e01600ab053c29014109d04b024a117082034412a09203901bc0c606002f01740b605a02c81600ae05602a80e806e02b014009804a023011008404001f00f007402c013008804001c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
def record041_frame002_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b64ad94aba5192188fa47323511828ac44d22210ec864429210903e80d3f49f5cf8c7a53c996948464121ec0f187643a01c68de06cc3541a10cc063c30e1758b6456a2a314909c44be21410787e83e61eb0f287783ac1d00e487083761b40d6867c33018a0c085e82d81650b005642a414b0a204d825e121086035412a09203901bc0c606002f01740b605a02c81600ae05602a80e806e02b014009804a023011008404001f00f007402c013008804001c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record041_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record041_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 2)
      (record041.inverseMaps 2) record041_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record041_frame002_links_0000 record041_frame002_links_0064)
theorem record041_frame002_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 2 :=
  of_group record041 2 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record041_frame002_indices record041_frame002_graph record041_frame002_links
def record041_frame003_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1bd2dd4f89ed3926f4d69a5332624c09752d2574a894525a484848f51d23446275cbb1752d85a4b29632c0570ad1572a8544a714b28a5089e1372684b89590d21840c800fc1f43dc798f11dc3ac740e51c43706c8d319c32c628c21823005f8be17a2ec5d0b816a2b44888e0e01b43085e0b816c2c8580ae1582a8540a60e81b82b050098128230440841001f03c0740b0130220400700d01802c050090100180280400600800800 } : Fields).get c.val)
theorem record041_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record041_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record041) (record041.maps 3)
      (record041.inverseMaps 3) record041_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record041_frame003_links_0000 record041_frame003_links_0064)
theorem record041_frame003_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 3 :=
  of_group record041 3 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record041_frame003_indices record041_frame003_graph record041_frame003_links
def record041_frame004_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17eea5a49fa4bd1d88db46322d514888f442a1d50ba8464192080ffc7ec3e91ef8f5277d3b5994ca9253b28113d09cc4d726492ec9644a524992048e246422490f084c4172038f9c7b63611a80c5460c2f61740b645922bf1588a74514278136894848e23111108443e41e50eb071836a1a80ce06142f2164098832012a09203901bc0c606002f01740b605a02c81600ae05602a80e806e02b014009804a023011008404001f00f007402c013008804001c00d006002c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record041_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record041) (record041.maps 4) (record041.inverseMaps 4) record041_frame004_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record041) (record041.maps 4) (record041.inverseMaps 4) record041_frame004_indices (Fin.ofNat record041.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record041_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record041) (record041.maps 4)
      (record041.inverseMaps 4) record041_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record041_frame004_links_0000 record041_frame004_links_0064)
theorem record041_frame004_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 4 :=
  of_group record041 4 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record041_frame004_indices record041_frame004_graph record041_frame004_links
def record041_frame005_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa9094684e84581c8097f67e07cf7be7a879b79078076f76073b7277006eb6d96b36a05e05024fa4da4cc4bc4ac49e48f48047546d4604524444254153f53e43d63b63a633832d3052f52e62d92cd2bd2ac2a029628627526724923921a2071f81d91cb1c21ba1ae1a019117316514611c0b408f08c07006d06105e05c05b05905805705605505405303a03702b02802602502302202102001f01e01d01601301101000e00d00c00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record041_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record041) (record041.maps 5) (record041.inverseMaps 5) record041_frame005_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record041) (record041.maps 5) (record041.inverseMaps 5) record041_frame005_indices (Fin.ofNat record041.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record041_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record041) (record041.maps 5)
      (record041.inverseMaps 5) record041_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record041_frame005_links_0000 record041_frame005_links_0064)
theorem record041_frame005_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 5 :=
  of_group record041 5 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record041_frame005_indices record041_frame005_graph record041_frame005_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (Fin.cases (record041_frame002_supported hcells) (Fin.cases (record041_frame003_supported hcells) (Fin.cases (record041_frame004_supported hcells) (Fin.cases (record041_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x230916089e446a1ed0e275b3a69d08e6e72c39297a8bb65cf2e216e0b625532a014c4a4651928413e49d44db269130895e4a02490eb473638c1bd8db06c434e19c8c9462630617a0b8c5a62c215c096448e23411107f43dc1e00e8870c3721a70ca060c2e61640a7850026005902c015c0ac043021010408002a01480a004e021010007c03c011008003c01c00c00580280120060028010006000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
def record042_frame002_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x2789da739c66e9ae298962287a1b861d774dd0731c9719b06a5a36759b6659765593645865f9775c1384d1304b5294991b4550f4250640d003f8fb3e4d8350d0330c5304bd2e8b62ccaa28c9d25c8f220831f83a0e4380dc340cc320c427098250901e0741c06c110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record042_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record042_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record042) (record042.maps 2)
      (record042.inverseMaps 2) record042_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record042_frame002_links_0000 record042_frame002_links_0064)
theorem record042_frame002_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 2 :=
  of_group record042 2 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record042_frame002_indices record042_frame002_graph record042_frame002_links
def record042_frame003_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x1926418e6318a621705b96c5a9685993f4f1394d9334c1214791b46116451124410e43108411003f0d7350d1338cb320c42fcba2d4b22c0ae2b0aa2a09624c902348821884208801f87a1d4701ac681946217c330c8310c02d0b02b0a82408c220841b06819060110400f0380c02c0a024060140400c00 } : Fields).get c.val)
theorem record042_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record042_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record042) (record042.maps 3)
      (record042.inverseMaps 3) record042_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record042_frame003_links_0000 record042_frame003_links_0064)
theorem record042_frame003_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 3 :=
  of_group record042 3 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record042_frame003_indices record042_frame003_graph record042_frame003_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (Fin.cases (record042_frame002_supported hcells) (Fin.cases (record042_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x9d39c99c29b79ab99f79b79078076f76075066966165b65364863a47546d46045244443637936d36035234533a32d3203133052f52e72a029628627526725a2472372262182071f81e71d91c21ba1ae1a019118317116315414413512911a10907907807707605705605505404304204104002102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa73a67a63a58a48a3e8108007f77ea7d47c06bf6b16aa6a069568b4b34a449b4904824773bd3ae3a439738837b36b35834d34133131f2c72b72ad2a12932862732632532442322232132011e21d51cd1c41b51a819618517616915514313312307b07a07907805905805705604304204104002102001f01e01501401301201101000f00e00d00c00b00a009006005004003000 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
def record043_frame003_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xda364d835cd6354aeab6acaadaa6a59926197a5b96255711c16f9b96d5b15c56d5a5655815b55d545454e52946491214791a4591243507404fc3d4f03ace837cdb35cd333ccb314bd2d4af29ca0264941685916057104400fc3e0e8390e0370842007c1e0541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record043_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record043) (record043.maps 3)
      (record043.inverseMaps 3) record043_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame003_links_0000 record043_frame003_links_0064)
theorem record043_frame003_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 3 :=
  of_group record043 3 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record043_frame003_indices record043_frame003_graph record043_frame003_links
def record043_frame004_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x169eb405992c9d632b1346122c113c88d43da1c4eb674d3a11cdce5872528c94209f24ea26d93488023f01f08f5078a3bd1d68e6c71837b1b60d8860c2f41718b4c5842b81530a484fe26d12c891c4682220fe87b83c01d10e186e43521960c205d02c814f0a004c00f607a03c81e00b205802b8158086042020810004202000f807802a0140098048022010007803801a00c00580280120060028010006000 } : Fields).get c.val)
theorem record043_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record043) (record043.maps 4) (record043.inverseMaps 4) record043_frame004_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record043) (record043.maps 4) (record043.inverseMaps 4) record043_frame004_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record043) (record043.maps 4)
      (record043.inverseMaps 4) record043_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame004_links_0000 record043_frame004_links_0064)
theorem record043_frame004_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 4 :=
  of_group record043 4 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record043_frame004_indices record043_frame004_graph record043_frame004_links
def record043_frame005_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xc8f1ec6b15c470d9e2769ce719ba6b8a62588a1e86e1866d9965d9564d915494d521444fd3b4e1344c12d4a52641903400fe3ecf93c4ea394e0360d4340cc314c12f4ba2d8b32aca42789823c8820c7e1404f1384d0e8390e0370d0330c8310781d0701b0541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record043_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record043) (record043.maps 5) (record043.inverseMaps 5) record043_frame005_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record043) (record043.maps 5) (record043.inverseMaps 5) record043_frame005_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record043) (record043.maps 5)
      (record043.inverseMaps 5) record043_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame005_links_0000 record043_frame005_links_0064)
theorem record043_frame005_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 5 :=
  of_group record043 5 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record043_frame005_indices record043_frame005_graph record043_frame005_links
def record043_frame006_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x816027fdfc7e5f6649906398c629885c16e5b16a5a16645914449104390c3b8ea398e2378da35cd4344ce32cc82c8b02b8ac2a8a8294a127499258932408d22086210822007e1ec761c46c1a0651885f1244811c460cc320c4300b42c0ac2a06c1a064180541404c120441003c0e0340c02c0a024060140400c00 } : Fields).get c.val)
theorem record043_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record043) (record043.maps 6) (record043.inverseMaps 6) record043_frame006_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record043) (record043.maps 6) (record043.inverseMaps 6) record043_frame006_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record043) (record043.maps 6)
      (record043.inverseMaps 6) record043_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame006_links_0000 record043_frame006_links_0064)
theorem record043_frame006_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 6 :=
  of_group record043 6 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record043_frame006_indices record043_frame006_graph record043_frame006_links
def record043_frame007_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0832.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0832.count (({ width := 9, code := 0x32992c8e431d8ca8d429d4da652a5b2b954a24b236d361acd4693416eb55a2c960ad562a952a752a89369a4c259269248231148942a09007e3d9e8f076399c8dc6b3499ccc623017c88432110470371b0d45e2e168b03e1e0e8702a14098482210078381a0c058281206028100600 } : Fields).get c.val)
theorem record043_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record043) (record043.maps 7) (record043.inverseMaps 7) record043_frame007_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record043) (record043.maps 7) (record043.inverseMaps 7) record043_frame007_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record043) (record043.maps 7)
      (record043.inverseMaps 7) record043_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame007_links_0000 record043_frame007_links_0064)
theorem record043_frame007_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 7 :=
  of_group record043 7 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0832
    Papers.RationalityTen.SharedFrameCatalogue.group0832_facts record043_frame007_indices record043_frame007_graph record043_frame007_links
def record043_frame008_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x180ebf35ee2f21764b9d44421d90c885242120c0da66bf3541a50cfc6691aa0d0866031e1870bf0472232115889043a21610788204021fa0f987b03921c20dd86d035a1a60ce865831e1880c085e82e616c0b005642a414b0a204f426812d093047c230111085040c0f607a03c81e00b205802b8158086042020810004202000f807802a0140098048022010007803801a00c00580280120060028010006000 } : Fields).get c.val)
theorem record043_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 8) (record043.inverseMaps 8) record043_frame008_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 8) (record043.inverseMaps 8) record043_frame008_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 8)
      (record043.inverseMaps 8) record043_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame008_links_0000 record043_frame008_links_0064)
theorem record043_frame008_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 8 :=
  of_group record043 8 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record043_frame008_indices record043_frame008_graph record043_frame008_links
def record043_frame009_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0831.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0831.count (({ width := 8, code := 0x9e9c9b9a99988b8a888786857d7b7a7978776a69676665645e5d5c5a5958575655535251504f4e4c4b4a49474544434241403e3d3c3a39383736353433312f2e282726252221201f1e1d1c1b18171615131211100f0e0d0c0b0a0908070504030200 } : Fields).get c.val)
theorem record043_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0831.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0831.localPairCheck (smallEmbedding record043) (record043.maps 9) (record043.inverseMaps 9) record043_frame009_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0831.localPairCheck (smallEmbedding record043) (record043.maps 9) (record043.inverseMaps 9) record043_frame009_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0831.localPairCheck (smallEmbedding record043) (record043.maps 9)
      (record043.inverseMaps 9) record043_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame009_links_0000 record043_frame009_links_0064)
theorem record043_frame009_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 9 :=
  of_group record043 9 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0831
    Papers.RationalityTen.SharedFrameCatalogue.group0831_facts record043_frame009_indices record043_frame009_graph record043_frame009_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (Fin.cases (record043_frame003_supported hcells) (Fin.cases (record043_frame004_supported hcells) (Fin.cases (record043_frame005_supported hcells) (Fin.cases (record043_frame006_supported hcells) (Fin.cases (record043_frame007_supported hcells) (Fin.cases (record043_frame008_supported hcells) (Fin.cases (record043_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7066f06e26125fc5ee5c05b45ad59e59759058257b5744bb4af4a549a48e4823b33a739d39238637a35534f34834233d33732f32832131b31430d3063002ad29028225523822a21b21520e1eb1d21c61ba18e18517c15513c13011b1121091010db0c60c207006f06e05d05c05b05805705603903803703602602502402302102001f01e01401301201000f00e00b00a009008005004003001000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x60d30017daa7c532a97d31c92c47423490e283240ea00cfe26a434b1a14cf2668330176cb885b12cb95ecaca55629a1498a104ea26913089404922370f8478a3bd1c60db06c433b1938c545c62c215c0a484fe26d12c06e43501970b1854024210e080036012008e04681b00d606a030017c0b805b02b81580a803501a00cc06402a014009c04c024011808403e01e00e0050026012008003c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb135feb7cdf9a33223bc568810e60a3fd7ecfb5f23606b4d51a5340670bc5722d8590af956aa352aa2d40a724c495d2323f4567c8f29dd3926ecd91a1334640bf9702ce554a59442723e0788ec1b6354630c01762ac3f87d0f8194320630b41642b0550a2140270350680cc1902a05009c130240460840f81e0380500981202003c0700b0140240380400600800800 } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record045_frame002_links_0000 record045_frame002_links_0064)
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
def record045_frame003_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x658328d92aacd55faae137a95348ca42114086642aa12508667b33a19b8cce66032c9748b625892b61544a6a52428413e89be4c4254125c8f646d22f8f0072a37e1a78cc063e2fc1760b6c55c28f13f096c49623a118068831617b0a284ec23010807f036c12008e04681b00d606a030017c0b805b02b81580a803501a00cc06402a014009c04c024011808403e01e00e0050026012008003c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record045_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record045_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record045) (record045.maps 3)
      (record045.inverseMaps 3) record045_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record045_frame003_links_0000 record045_frame003_links_0064)
theorem record045_frame003_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 3 :=
  of_group record045 3 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record045_frame003_indices record045_frame003_graph record045_frame003_links
def record045_frame004_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x94d27e4bc2f85108df03be74ce75bd3626b2d45a5ade5b4b59692ce594a7546a7d4ec9b130a5c4989091b22c438855029f93da6fcd61a432a624c01702d2574a814627c4c89491f22e3906e8d619030c590ab1542603c0770ec18c310610ae1582985209c134258330640c41802904e098128230440800f01d0360500981202003c0700b0140240380400600800800 } : Fields).get c.val)
theorem record045_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record045_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 4)
      (record045.inverseMaps 4) record045_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record045_frame004_links_0000 record045_frame004_links_0064)
theorem record045_frame004_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 4 :=
  of_group record045 4 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record045_frame004_indices record045_frame004_graph record045_frame004_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (Fin.cases (record045_frame003_supported hcells) (Fin.cases (record045_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2f31748b865b12ce9624af256c2af9544a865352921458a104fa276137c9a44c425b12a092e48923d91b48ca46022d91587da3d51e00ea472a37e1b68d7c69e33f1980c7c6182fc1760b6c5982be1570a7851e27e135896c49623a11888a844621c0c485dc2ca1520a204e025a12108383ec1e00e401500a40500270130094048023010808003e01e00a8050026012008804001e00e006002c014009 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x45289510a1a424835052064047ecf99ee3d2798f19e03bc768eb1cf38e708de9ba36e6d0d81ad35469ccf99a326630c217b2e85bcb41612b2540a41442804ec9c1332584948e914218420820ff1f63dc798ee194310600b91662b4548a213224c4788805009c1302504808c1102103e0780e81c02a050098120220400780e01802c05009 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
def record046_frame003_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2f19748b805ac2cc9618ae85612a794f4a5651828193c89be4cf25f12b093448823b919c8a644121810848204001f78f7c6e83631a88cf46543171828bc85c02ce15e0aa4528283138098049e23d11588644101f80f207483821b20d08644300170095849023a11608784242060fc07703a01c40dc01500a40500270130094048023010808003e01e00a8050026012008804001e00e006002c014009 } : Fields).get c.val)
theorem record046_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record046) (record046.maps 3)
      (record046.inverseMaps 3) record046_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame003_links_0000 record046_frame003_links_0064)
theorem record046_frame003_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 3 :=
  of_group record046 3 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record046_frame003_indices record046_frame003_graph record046_frame003_links
def record046_frame004_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x60cbf97b2ee5ccb7d6c2d0592b0d5f2bb562a9d5029a520a254127a4ea9c132a5a4a2921202394688bd031fe3ec7b8f31df3ac73ce41c03766d8d59a032e638c297d2ec5c0b59682bc550a69472804e49a12f1f63d0768e61be360688cd1822e8598af0540a41402704c094120230420800f81e02a050098120220400780e01802c05009 } : Fields).get c.val)
theorem record046_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record046) (record046.maps 4)
      (record046.inverseMaps 4) record046_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame004_links_0000 record046_frame004_links_0064)
theorem record046_frame004_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 4 :=
  of_group record046 4 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record046_frame004_indices record046_frame004_graph record046_frame004_links
def record046_frame005_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1062.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1062.count (({ width := 8, code := 0x6867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d262524232221201f1d1c1b1a17161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record046_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1062.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1062.localPairCheck (smallEmbedding record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1062.localPairCheck (smallEmbedding record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1062.localPairCheck (smallEmbedding record046) (record046.maps 5)
      (record046.inverseMaps 5) record046_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame005_links_0000 record046_frame005_links_0064)
theorem record046_frame005_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 5 :=
  of_group record046 5 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1062
    Papers.RationalityTen.SharedFrameCatalogue.group1062_facts record046_frame005_indices record046_frame005_graph record046_frame005_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (Fin.cases (record046_frame003_supported hcells) (Fin.cases (record046_frame004_supported hcells) (Fin.cases (record046_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x280d3ac9bd4c325912a692b48ca4211a68b145021e10cc85542220f506c5c32ce9624abe54329a9458a104fa26912d895048923d91b48c045b22b0fb47aa3c01d48e546fc36d1af8d3c67e33018f8c305f82ec16d8b3057c2ae14f0a3c4fc26b12d892c474231115088c4381e00db868831a14708c04281b60d203081800be05d02e016c0b005702b00a4050027012809004602000f807802a0140098048022010007803801800b005002400a0040018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0xcc99131d620c017daf25dcba56e2cc58eaf95d2b5558aa151a21424835011f33dc798f19e03ac71ce11ba36e6d0d69aa34e67ccd193318610bd9742de5a0b09592a0520a21402764e09992c24a4748a10c2104107f8fb1ee3cc770e41b0340660b513c26c420810a61482884f09c1342504909009c130250460881081e03a0700a8140260480881001e0380600b0140240280400600800800 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5a4aff58ea5cfa9a32da524778ad1021cc0a806ff9f6be47bcf4dc2b756dcd81a5340658c85872f15c8b61642be55aa8d4aa8b4e493923a2b44684cf91e53ba724dd9b2342668c81702b85309c9282303e0788ec1b6354630c01762d8410800fe1f0348670ca18c2d0590ac1542804f09c0e41c03606a0d01902a05009c130240460840f01d0380500981202003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
def record048_frame002_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x74672971870567663d61b6065c458c56855b52e52852251450e5074fb48146b46044d42e42240c3ff3ec3c23b23a038a37536335333e3333172ff2f92e62e02d529427b27025123d23221720a1fa1d01ba1a818e17d16913512611e0fa0f20d50cb0c60c108c08b08a08706e06c06a06805e05d05a05905405305203803703503403303102a02802702602402302101e01d01c01401301201000f00e00b009008007004003002001000 } : Fields).get c.val)
theorem record048_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record048) (record048.maps 2)
      (record048.inverseMaps 2) record048_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame002_links_0000 record048_frame002_links_0064)
theorem record048_frame002_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 2 :=
  of_group record048 2 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record048_frame002_indices record048_frame002_graph record048_frame002_links
def record048_frame003_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0375.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0375.count (({ width := 8, code := 0xb1b0afaba6a5a3a09e9d9a98949392908f8e8d8584838281807f7e7b79787776757473716f6b696865646361605f5e5d5c5a59575352504e4c4b47464542413f3e3d3c39383736333231302e2d2c2b292827232221201f1e1b1a19181716141312110f0e0d0c0b0a080706050403020100 } : Fields).get c.val)
theorem record048_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record048) (record048.maps 3)
      (record048.inverseMaps 3) record048_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame003_links_0000 record048_frame003_links_0064)
theorem record048_frame003_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 3 :=
  of_group record048 3 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0375
    Papers.RationalityTen.SharedFrameCatalogue.group0375_facts record048_frame003_indices record048_frame003_graph record048_frame003_links
def record048_frame004_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0447.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0447.count (({ width := 8, code := 0xb1b0afaba6a5a3a09e9d9a98949392908f8e8d8584838281807f7e7b79787776757473716f6b696865646361605f5e5d5c5a59575352504e4c4b47464542413f3e3d3c39383736333231302e2d2c2b292827232221201f1e1b1a19181716141312110f0e0d0c0b0a080706050403020100 } : Fields).get c.val)
theorem record048_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record048) (record048.maps 4) (record048.inverseMaps 4) record048_frame004_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record048) (record048.maps 4) (record048.inverseMaps 4) record048_frame004_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record048) (record048.maps 4)
      (record048.inverseMaps 4) record048_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame004_links_0000 record048_frame004_links_0064)
theorem record048_frame004_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 4 :=
  of_group record048 4 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0447
    Papers.RationalityTen.SharedFrameCatalogue.group0447_facts record048_frame004_indices record048_frame004_graph record048_frame004_links
def record048_frame005_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xcb0623b06980aac5532a90946897b48b23f51ec85c427210103880e4001f9cd7c68f33f9974c5c61e30197f8be458e2b91558a7251d28093e09dc4e925291948b8436216906873c37e1b78cf863c30f17e8bd85e028d13289304562120fd06483001760a7851424c11808483e412809104802340e006e03601a80c005f02e016c0ac05502a00e407003601a80d006402a014009c04c024011808403c01d00e0050026012008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record048_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record048) (record048.maps 5) (record048.inverseMaps 5) record048_frame005_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record048) (record048.maps 5) (record048.inverseMaps 5) record048_frame005_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record048) (record048.maps 5)
      (record048.inverseMaps 5) record048_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame005_links_0000 record048_frame005_links_0064)
theorem record048_frame005_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 5 :=
  of_group record048 5 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record048_frame005_indices record048_frame005_graph record048_frame005_links
def record048_frame006_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x4718b91261ec067e2f89ec3a570add9b934d68cd0197b29642c496b2c557ead5532a0528a414326d4ce97128a464708c915a264247d8f99dc3ac710d119431c60cbd9752d85a4b21492724b48c11020438c700da19231c5b8b215a2a04087f0fc1ec348670cc1902d85a0b015c290510a00e41c03606a0d01902a05009c130240460840f01d0380500981202003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record048_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record048) (record048.maps 6) (record048.inverseMaps 6) record048_frame006_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record048) (record048.maps 6) (record048.inverseMaps 6) record048_frame006_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record048) (record048.maps 6)
      (record048.inverseMaps 6) record048_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame006_links_0000 record048_frame006_links_0064)
theorem record048_frame006_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 6 :=
  of_group record048 6 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record048_frame006_indices record048_frame006_graph record048_frame006_links
def record048_frame007_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x5139eb3966ec7e8bb12220c127e8f89ef3b3760ea1cd395724e159531b628c157a2eb5b4b5566aad546a4542a7a4d89952ea5848a8ad12a1141e80cee1cc3886c4d1199314614c09632a051c9c92e23c3dc760e61a03305e0b61642b0410800fe1f4350690ce1942e85c0b41642a0530a40e01b8350680cc1882a05009c130240460840f01d0380500981202003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record048_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record048) (record048.maps 7) (record048.inverseMaps 7) record048_frame007_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record048) (record048.maps 7) (record048.inverseMaps 7) record048_frame007_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record048) (record048.maps 7)
      (record048.inverseMaps 7) record048_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame007_links_0000 record048_frame007_links_0064)
theorem record048_frame007_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 7 :=
  of_group record048 7 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record048_frame007_indices record048_frame007_graph record048_frame007_links
def record048_frame008_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0359.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0359.count (({ width := 8, code := 0xa7a6a5a29d9c9a98969592918d8c8b8a8988877f7e7d7c7b7a79787674737271706f6e6c6b6765646261605e5d5c5b5a5957565551504e4d4b4a46454442413f3e3d3c39383736333231302e2d2c2b292827232221201f1e1b1a19181716141312110f0e0d0c0b0a080706050403020100 } : Fields).get c.val)
theorem record048_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0359.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0359.localPairCheck (smallEmbedding record048) (record048.maps 8) (record048.inverseMaps 8) record048_frame008_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0359.localPairCheck (smallEmbedding record048) (record048.maps 8) (record048.inverseMaps 8) record048_frame008_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0359.localPairCheck (smallEmbedding record048) (record048.maps 8)
      (record048.inverseMaps 8) record048_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame008_links_0000 record048_frame008_links_0064)
theorem record048_frame008_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 8 :=
  of_group record048 8 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0359
    Papers.RationalityTen.SharedFrameCatalogue.group0359_facts record048_frame008_indices record048_frame008_graph record048_frame008_links
def record048_frame009_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0298.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0298.count (({ width := 8, code := 0x8281807d7978767473726f6e6d6c6b6a696867605f5e5d5c5b5a5957565554535251504e4d4c4b4a4948474645444342413f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record048_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0298.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0298.localPairCheck (smallEmbedding record048) (record048.maps 9) (record048.inverseMaps 9) record048_frame009_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0298.localPairCheck (smallEmbedding record048) (record048.maps 9) (record048.inverseMaps 9) record048_frame009_indices (Fin.ofNat record048.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record048_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0298.localPairCheck (smallEmbedding record048) (record048.maps 9)
      (record048.inverseMaps 9) record048_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record048_frame009_links_0000 record048_frame009_links_0064)
theorem record048_frame009_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 9 :=
  of_group record048 9 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0298
    Papers.RationalityTen.SharedFrameCatalogue.group0298_facts record048_frame009_indices record048_frame009_graph record048_frame009_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (Fin.cases (record048_frame002_supported hcells) (Fin.cases (record048_frame003_supported hcells) (Fin.cases (record048_frame004_supported hcells) (Fin.cases (record048_frame005_supported hcells) (Fin.cases (record048_frame006_supported hcells) (Fin.cases (record048_frame007_supported hcells) (Fin.cases (record048_frame008_supported hcells) (Fin.cases (record048_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1588aab55325f12d69594a424d925889e43da1c508a83040d9fc8fb87c636a9aecd645a62cb9628af656e2b293e49b64d2256927892046f22f91408023f01f08f5078a3bd1d68e6c71837b1b60d886a033b1938c545c62c215c0a9c48e23411107f43dc1e00e8870c3721a90cb06102e811106b83240e006f03701780ba05c02d81600ae05601c00dc06c026012809004602000f807802a0140098048022010007803801600a004802000c005002000c002000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
def record049_frame002_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xbfef8bd6aeaaaa6a8a9ea6a739ba6b96a5292a3d8e23382a03801c4709c06f9bc6e99764d915f5765bd645855e5494d521444fd3b4e1344c12d4a526475164410a400fb3e4f2350d0330c5304bd2e8b62ccab2909e260741845d12c4a1243f0f83d0f0390e0370bc2e0b423088210801d0701b0541404c120441003c0e02c0a02408018050100300400 } : Fields).get c.val)
theorem record049_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record049_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record049) (record049.maps 2)
      (record049.inverseMaps 2) record049_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record049_frame002_links_0000 record049_frame002_links_0064)
theorem record049_frame002_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 2 :=
  of_group record049 2 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record049_frame002_indices record049_frame002_graph record049_frame002_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (Fin.cases (record049_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a1562a8952fa6452d6959473a2ad13086442120c10167f93f39f58f9057d2aa94ac8ba4372128ecc6ee3641980c385f82d71628acc54429411c88c845622410e88584101fa0f6078c3aa1ce0e487083761b40d6869833a1960c786202f81520a204f426a11908983f81ec0db04702340da06b03501840c005f02e016c0b005702b015006a03301900a4050027012008c04001f00f007002a014009804802200f007003001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x32354509ae4d3a6813329924c5a5f52de9614ac2529286930491246d21690447ea3dd1e26962f19748b805ac2cc9618ac253d28c140c9be4cf24d11dc8ce44121810848224021ba0d8c6a233d1950c5c5e42ce1548a504e026011588203f01d20e086c83441930ab053c29014109d04cc2140f6077835c11c08d03581a80c4061030017c0bc05c02d81600ae05602a00cc06402a01480a004e026012008c04001f00f007002a014009804802200f007002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
def record051_frame002_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a14be9b64d126452fc96b4aca4c92188e746922ad13086442120c10167f93f39f60f9052b24111b88ba44a21b90947fc3d81d98e786ee3641980c385f82d71628acc54829411c88c845622410e88584101fa0f6078c3aa1ce0dd86b434c1960c7862030417c0b005642a414b0a204f42260fe07b836c11c08d03581a80c4061030017c0bc05c02d81600ae05602a00cc06402a01480a004e026012008c04001f00f007002a014009804802200f007002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record051_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 2)
      (record051.inverseMaps 2) record051_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame002_links_0000 record051_frame002_links_0064)
theorem record051_frame002_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 2 :=
  of_group record051 2 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame002_indices record051_frame002_graph record051_frame002_links
def record051_frame003_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2fb54be9d54e1a6c934c9954c725ad29092c48ba3a11a489e43da1c508e83240ea020fe86602f5176cb9e5c42dc16c4b2e57b2b29558a6852627c936c9a44af25012489064712008fc07c23d41e28ef473637b1b10d4064e3151718b0857029213f89b44b42490fe87b83c01d10e186e42a2121088836011c08d03581a80c4061030017c0bc05c02d81600ae05602a00cc06402a01480a004e026012008c04001f00f007002a014009804802200f007002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record051_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record051) (record051.maps 3)
      (record051.inverseMaps 3) record051_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame003_links_0000 record051_frame003_links_0064)
theorem record051_frame003_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 3 :=
  of_group record051 3 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record051_frame003_indices record051_frame003_graph record051_frame003_links
def record051_frame004_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x1916d2578add596ad54ea894e293511a073b26ecc7967296484808e31a632bb6710e01bc36f6c6d65a6b3e654c75852ff5d8b6d672bb55ca8d4e2994dc9912ca4f4868e11421b40e7ecf51dd3966f0d799c324614bf97b2c6570a91472784c4750d018c2903d0790c21802c0570ac1542a0520a21382684c0940cc1902a0520a01382604808c1001f03c0700a8140260480880f01c02c0500900e0180280400600800800 } : Fields).get c.val)
theorem record051_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record051) (record051.maps 4) (record051.inverseMaps 4) record051_frame004_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record051) (record051.maps 4) (record051.inverseMaps 4) record051_frame004_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record051) (record051.maps 4)
      (record051.inverseMaps 4) record051_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame004_links_0000 record051_frame004_links_0064)
theorem record051_frame004_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 4 :=
  of_group record051 4 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record051_frame004_indices record051_frame004_graph record051_frame004_links
def record051_frame005_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x125e11bfc7eefc9f6be67c0f55e53be76ce99ceb8d704de9b63626b2d4da6aca546a754b28d5089f53b26c4c2971262424628990e20f40a7e4fa1ef394710df9b7358690cd1903005e4b495d2a05189f13225247c8c9151fc3e87a8ef1d2390620b215a2603b8760c41842c8580ae1582a8530a413c2704d0960c41802905009c130250460880f81e03a06c0a8140260480880f01c02c0500900e0180280400600800800 } : Fields).get c.val)
theorem record051_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record051) (record051.maps 5) (record051.inverseMaps 5) record051_frame005_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record051) (record051.maps 5) (record051.inverseMaps 5) record051_frame005_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record051) (record051.maps 5)
      (record051.inverseMaps 5) record051_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame005_links_0000 record051_frame005_links_0064)
theorem record051_frame005_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 5 :=
  of_group record051 5 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record051_frame005_indices record051_frame005_graph record051_frame005_links
def record051_frame006_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0643.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0643.count (({ width := 9, code := 0x449f8f278bc1deee76ba9d0e672381bcda6c35da6d167b3998bb58ac15eae56ab152a752a8d3e9d4ca5d2c92482391a8b43215088341204fc7c3d1e0e872371b0d6673298cc4602d968b2582b958a250279388e46200fc783b1d0e470361a8c86230170a450251208c44210f878361a0c85c2a1409848220f0702c1409038180a04018080200 } : Fields).get c.val)
theorem record051_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record051) (record051.maps 6) (record051.inverseMaps 6) record051_frame006_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record051) (record051.maps 6) (record051.inverseMaps 6) record051_frame006_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record051) (record051.maps 6)
      (record051.inverseMaps 6) record051_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame006_links_0000 record051_frame006_links_0064)
theorem record051_frame006_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 6 :=
  of_group record051 6 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0643
    Papers.RationalityTen.SharedFrameCatalogue.group0643_facts record051_frame006_indices record051_frame006_graph record051_frame006_links
def record051_frame007_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0xff9c6b6f6d4d95b0b5d6b2d41a3b40674cc595b1f630c49843025fabe57a24f4588910e215420835039fc3ee7bcf21dd39c710e09b2356698d119d3005e8ba1702d0584ab15028a4f89812923c4688a1071fc3e47b0f21be3686a8d119831c5a0a814c2583806f0be1782d0590b015c2b0540a61402784e0980bc1702804e098128240440840f01d0380680a8140260480880f01c02c0500900e0180280400600800800 } : Fields).get c.val)
theorem record051_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record051) (record051.maps 7) (record051.inverseMaps 7) record051_frame007_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record051) (record051.maps 7) (record051.inverseMaps 7) record051_frame007_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record051) (record051.maps 7)
      (record051.inverseMaps 7) record051_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame007_links_0000 record051_frame007_links_0064)
theorem record051_frame007_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 7 :=
  of_group record051 7 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record051_frame007_indices record051_frame007_graph record051_frame007_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (Fin.cases (record051_frame002_supported hcells) (Fin.cases (record051_frame003_supported hcells) (Fin.cases (record051_frame004_supported hcells) (Fin.cases (record051_frame005_supported hcells) (Fin.cases (record051_frame006_supported hcells) (Fin.cases (record051_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x4aca4d92588c2458227911a87b4389fc8fb87c63a11cb0e4a6f13701b54d8c6bb35918f0c546192c515b8aca5412991490a3250827c93a89b64d226012b493c490237917c8a038c1b60d886723251898c185e82e31698b085702a414809f44d624711a08883fa1ee0f007443861b90b303240ba05c02d81640b005702b010808204001c80e006e0360128090046021010007c03c010007803801800b005002400c005002000c002000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
def record052_frame002_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x4bb25a12c293e49ba4c125292248da3bd1d08e14049f8cf9e7753b01d38e70722386999cca263c2a794aca304f026e933497c4ac24d12208ee46722890fc85c41f2000fbc7be2e015e0aa450226e12f093c47a22b10c88203f01e20e806fc3601910c005c02ac14f0a4050427413308803440ba05c02d81640b005702b010808204001c80e006e0360128090046021010007c03c010007803801800b005002400c005002000c002000 } : Fields).get c.val)
theorem record052_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record052_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record052) (record052.maps 2)
      (record052.inverseMaps 2) record052_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record052_frame002_links_0000 record052_frame002_links_0064)
theorem record052_frame002_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 2 :=
  of_group record052 2 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record052_frame002_indices record052_frame002_graph record052_frame002_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (Fin.cases (record052_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2bad588ab04bfa5612888a044ca248e4e7163839bdcdce6d73519a04ce464a31b9898ba45c12d91688b245822a714b0a3a4f5271134493a49624792208f64752378d5c65831915c8aa453228a13d09ac4ae24811c08a443a1d60e306d834e1970c405d02ca1550a304e81ee0f007483881a806c03581a80ba05c02d80e407003701b00d006603201500a40500270128090046010007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6942e754bea20506239d15289644421d90c885242120c0fb27c833494ac9d84d81d98dd46c43541a10cc063c30e17e0a9452823911908ac44821d10b07b03c81dd0e487083761b40d6869833a1960c7862030617c0b305802b21520a5851027a134096849823e11a08983f411c08d03c81e00d606a02e016c0b205802b81580a804102000cc064024011808404001f00f007002a014009804801e00e006803001600a004801c00c005002000c002000 } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
def record054_frame002_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f6ac4d4bea1e505a4b11cc8d046122c113c88d43da1c50127f43929980c5661a2b294c8a4851928413e49d44db26912108e24011f80f847a83c51de8d886a233c1830bd05c62d31610ae054c29213f89b44b624910787f43dc1e00e8870c3721a90cb06102e81660a8848011c08d03c81e00d606a02e016c0b205802b81580a804102000cc064024011808404001f00f007002a014009804801e00e006803001600a004801c00c005002000c002000 } : Fields).get c.val)
theorem record054_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record054_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record054) (record054.maps 2)
      (record054.inverseMaps 2) record054_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record054_frame002_links_0000 record054_frame002_links_0064)
theorem record054_frame002_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 2 :=
  of_group record054 2 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record054_frame002_indices record054_frame002_graph record054_frame002_links
def record054_frame003_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa4e99f9038d28c07f77bb7a479b79078076f7607506ed6db63a59d56c55e4bd48c47c47546d4604524444363e63d837936d36035234533a2e72d82cc2a029628627526725a2472372262182091fa1cc1c21ba1ae1a019118317116315414413712b0fd08808707707606906805a05905705605505405204104003303202402302102001f01e01c01501401301200f00e00d00c00b00a009007006005004003001000 } : Fields).get c.val)
theorem record054_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record054_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record054) (record054.maps 3)
      (record054.inverseMaps 3) record054_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record054_frame003_links_0000 record054_frame003_links_0064)
theorem record054_frame003_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 3 :=
  of_group record054 3 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record054_frame003_indices record054_frame003_graph record054_frame003_links
def record054_frame004_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x684af3d560a7453125112108f6477239d1c08d9469232d1508a13bd19c8c6a62428e938099e4c726012e49644ac25292088f84031f50f4c7783a81c98c646062ef15c8aa453228a13d09ac4b224a11d08ac43a20e0f1875838c1b60d3865c3101760b3855c29013a095840011c08d03c81e00d606a02e016c0b205802b81580a804102000cc064024011808404001f00f007002a014009804801e00e006803001600a004801c00c005002000c002000 } : Fields).get c.val)
theorem record054_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record054) (record054.maps 4) (record054.inverseMaps 4) record054_frame004_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record054) (record054.maps 4) (record054.inverseMaps 4) record054_frame004_indices (Fin.ofNat record054.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record054_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record054) (record054.maps 4)
      (record054.inverseMaps 4) record054_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record054_frame004_links_0000 record054_frame004_links_0064)
theorem record054_frame004_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 4 :=
  of_group record054 4 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record054_frame004_indices record054_frame004_graph record054_frame004_links
def record054_frame005_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65f6155ab58757a50c4e84db4d44d04cb4c54c04bb49c4964423d43ae3a133130b2fe2f82f42f02eb2e52e02c12bc28928027526925c2502132071fa1db1d51cc1c41b91b11a219718f18417c17315414b14613e13412c12111310a0ff0f40ed0e50c408408307507406806705a05905705605505405203f03e03203102402302102001f01e01c01501401301200f00e00d00c00b00a009007006005004003001000 } : Fields).get c.val)
theorem record054_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record054) (record054.maps 5) (record054.inverseMaps 5) record054_frame005_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record054) (record054.maps 5) (record054.inverseMaps 5) record054_frame005_indices (Fin.ofNat record054.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record054_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record054) (record054.maps 5)
      (record054.inverseMaps 5) record054_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record054_frame005_links_0000 record054_frame005_links_0064)
theorem record054_frame005_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 5 :=
  of_group record054 5 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record054_frame005_indices record054_frame005_graph record054_frame005_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (Fin.cases (record054_frame002_supported hcells) (Fin.cases (record054_frame003_supported hcells) (Fin.cases (record054_frame004_supported hcells) (Fin.cases (record054_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x67066b6666626315f05bf5a65a259e55d52451750b5074c94bc4b149e49048547f43a3f93c43a93a63a237033d33332c32a2ec2e22db2ce2c32bc2b627826d26424622d22420a2061ed1d11b91a519117e17414212d12511e1060fe0ee0d50c909208708107f07e07307206b06906706406305b05a05705505405105004f04e04304203903703503203102902802502302201f01e01d01c01501401301101000e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
def record055_frame002_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6c26bc6b76b368563c6045ee5e95e55af55553d5225194da4c94bc4a549949348d4594163e03cd3c83c338c34833332131b2ed2de2d62c62bb2b82b428627a2712452302261fc1f41e41d51c41aa19918b18715f14613a12d1070fb0eb0cd0c509508c08608108007107006a06906706406305d05c05905705605305205105004104003903703503203102902802502302201f01e01d01c01501401301101000e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record055_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record055) (record055.maps 2) (record055.inverseMaps 2) record055_frame002_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record055) (record055.maps 2) (record055.inverseMaps 2) record055_frame002_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record055) (record055.maps 2)
      (record055.inverseMaps 2) record055_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame002_links_0000 record055_frame002_links_0064)
theorem record055_frame002_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 2 :=
  of_group record055 2 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record055_frame002_indices record055_frame002_graph record055_frame002_links
def record055_frame003_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0765.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0765.count (({ width := 8, code := 0xbfbebdbcb9b7b6b5b4b3aca8a7a4a29e9d9b989795938e8c8b8a8988827f7e7d7c797877767574736f6d6b6a6866656463615f5e5d5c5b575452504c4a4743413c3b3a393837363534333231302f2e2d2c2b2a2928272625242322211d1c1b1a191817161511100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0765.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record055) (record055.maps 3) (record055.inverseMaps 3) record055_frame003_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record055) (record055.maps 3) (record055.inverseMaps 3) record055_frame003_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record055) (record055.maps 3)
      (record055.inverseMaps 3) record055_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame003_links_0000 record055_frame003_links_0064)
theorem record055_frame003_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 3 :=
  of_group record055 3 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0765
    Papers.RationalityTen.SharedFrameCatalogue.group0765_facts record055_frame003_indices record055_frame003_graph record055_frame003_links
def record055_frame004_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0739.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0739.count (({ width := 8, code := 0xc8c7c6c5c2c0bfbebdbcb2aeadaaa8a4a3a19e9d9b99949291908f8e858281807f7c7b7a7978777672706e6d6b69686766646261605f5e585452504c4a4743413c3b3a393837363534333231302f2e2d2c2b2a2928272625242322211d1c1b1a191817161511100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0739.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record055) (record055.maps 4) (record055.inverseMaps 4) record055_frame004_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record055) (record055.maps 4) (record055.inverseMaps 4) record055_frame004_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record055) (record055.maps 4)
      (record055.inverseMaps 4) record055_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame004_links_0000 record055_frame004_links_0064)
theorem record055_frame004_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 4 :=
  of_group record055 4 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0739
    Papers.RationalityTen.SharedFrameCatalogue.group0739_facts record055_frame004_indices record055_frame004_graph record055_frame004_links
def record055_frame005_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0719.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0719.count (({ width := 9, code := 0x452271288c2202fc7cbe1eeee74399c2df6cb61acd3693419ac15d2d564b1582a948a24fa7934984ba592a9449a3516894320d027d3e1ecf2763a1cce4713599cc8612e168ac502711c8a4421908803f1f0f4783b1d0e470371b0d46833190c45e2e168b0562a1488842200f074381b0d06424110803c1c0c058281208038180a04018080200 } : Fields).get c.val)
theorem record055_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0719.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record055) (record055.maps 5) (record055.inverseMaps 5) record055_frame005_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record055) (record055.maps 5) (record055.inverseMaps 5) record055_frame005_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record055) (record055.maps 5)
      (record055.inverseMaps 5) record055_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame005_links_0000 record055_frame005_links_0064)
theorem record055_frame005_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 5 :=
  of_group record055 5 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0719
    Papers.RationalityTen.SharedFrameCatalogue.group0719_facts record055_frame005_indices record055_frame005_graph record055_frame005_links
def record055_frame006_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65965565064a6325f85bd59258957e5555185014ea4df4bb4b44ae4a249b4954904614223e63bb3b13a537b33c32530e3022e02d82d22c62c02bb2b728928027524922721d1ef1e41d51c41b119818617216813e12c1211140f60ec0d80bc0b809208a08608308207707606e06c06a06706605f05e05b05905805505405305204104003803603403103002902802502302201f01e01d01c01501401301101000e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record055_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record055) (record055.maps 6) (record055.inverseMaps 6) record055_frame006_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record055) (record055.maps 6) (record055.inverseMaps 6) record055_frame006_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record055) (record055.maps 6)
      (record055.inverseMaps 6) record055_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame006_links_0000 record055_frame006_links_0064)
theorem record055_frame006_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 6 :=
  of_group record055 6 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record055_frame006_indices record055_frame006_graph record055_frame006_links
def record055_frame007_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x145e8a511a1d3b25e48b8e51be3544c83b046034037c0f69e93c677cee5d9374676c2577aec5ceb0d4aa874f89e52e2584a49212023c46e831011f93b870cdc996320610ba9672b25389d9352264147e8f71ba354640b61602384588710a2103b8760dc1b4358680ce1802f85d0b61682b8560aa150218420720dc1a8320620a4140250460880f81e03a0700a8140260440800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record055_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record055) (record055.maps 7) (record055.inverseMaps 7) record055_frame007_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record055) (record055.maps 7) (record055.inverseMaps 7) record055_frame007_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record055) (record055.maps 7)
      (record055.inverseMaps 7) record055_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame007_links_0000 record055_frame007_links_0064)
theorem record055_frame007_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 7 :=
  of_group record055 7 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record055_frame007_indices record055_frame007_graph record055_frame007_links
def record055_frame008_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0440.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0440.count (({ width := 8, code := 0xa7a6a5a4a29e9b9998979592918f8e8d8c8b8988878684807d7b7a7977747371706f6e6d6b6a69686463625e5d5b57565453514e4c4a4948474543403e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161211100e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0440.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0440.localPairCheck (smallEmbedding record055) (record055.maps 8) (record055.inverseMaps 8) record055_frame008_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0440.localPairCheck (smallEmbedding record055) (record055.maps 8) (record055.inverseMaps 8) record055_frame008_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0440.localPairCheck (smallEmbedding record055) (record055.maps 8)
      (record055.inverseMaps 8) record055_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame008_links_0000 record055_frame008_links_0064)
theorem record055_frame008_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 8 :=
  of_group record055 8 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0440
    Papers.RationalityTen.SharedFrameCatalogue.group0440_facts record055_frame008_indices record055_frame008_graph record055_frame008_links
def record055_frame009_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0416.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0416.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0416.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0416.localPairCheck (smallEmbedding record055) (record055.maps 9) (record055.inverseMaps 9) record055_frame009_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0416.localPairCheck (smallEmbedding record055) (record055.maps 9) (record055.inverseMaps 9) record055_frame009_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0416.localPairCheck (smallEmbedding record055) (record055.maps 9)
      (record055.inverseMaps 9) record055_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame009_links_0000 record055_frame009_links_0064)
theorem record055_frame009_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 9 :=
  of_group record055 9 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0416
    Papers.RationalityTen.SharedFrameCatalogue.group0416_facts record055_frame009_indices record055_frame009_graph record055_frame009_links
def record055_frame010_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0407.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0407.count (({ width := 8, code := 0xdedddcdbdad7d3d0cfcdcbc7c6c3c2bfbebcbab8b7b6b3b0aca9a8a6a4a09f9c9b9897959391908f8b898883807d797775726f6c696665605b595853514e4947403f3e3d3c39383635343332302f2e2d2c2b2a292825242221201f1e1c1b1a19181716151411100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record055) (record055.maps 10) (record055.inverseMaps 10) record055_frame010_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record055) (record055.maps 10) (record055.inverseMaps 10) record055_frame010_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0407.localPairCheck (smallEmbedding record055) (record055.maps 10)
      (record055.inverseMaps 10) record055_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame010_links_0000 record055_frame010_links_0064)
theorem record055_frame010_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 10 :=
  of_group record055 10 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0407
    Papers.RationalityTen.SharedFrameCatalogue.group0407_facts record055_frame010_indices record055_frame010_graph record055_frame010_links
def record055_frame011_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0393.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0393.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0393.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0393.localPairCheck (smallEmbedding record055) (record055.maps 11) (record055.inverseMaps 11) record055_frame011_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0393.localPairCheck (smallEmbedding record055) (record055.maps 11) (record055.inverseMaps 11) record055_frame011_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0393.localPairCheck (smallEmbedding record055) (record055.maps 11)
      (record055.inverseMaps 11) record055_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame011_links_0000 record055_frame011_links_0064)
theorem record055_frame011_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 11 :=
  of_group record055 11 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0393
    Papers.RationalityTen.SharedFrameCatalogue.group0393_facts record055_frame011_indices record055_frame011_graph record055_frame011_links
def record055_frame012_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0371.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0371.count (({ width := 8, code := 0xa7a6a5a4a29e9b9998979592918f8e8d8c8b8988878684807d7b7a7977747371706f6e6d6b6a69686463625e5d5b57565453514e4c4a4948474543403e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161211100e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0371.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0371.localPairCheck (smallEmbedding record055) (record055.maps 12) (record055.inverseMaps 12) record055_frame012_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0371.localPairCheck (smallEmbedding record055) (record055.maps 12) (record055.inverseMaps 12) record055_frame012_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0371.localPairCheck (smallEmbedding record055) (record055.maps 12)
      (record055.inverseMaps 12) record055_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame012_links_0000 record055_frame012_links_0064)
theorem record055_frame012_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 12 :=
  of_group record055 12 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0371
    Papers.RationalityTen.SharedFrameCatalogue.group0371_facts record055_frame012_indices record055_frame012_graph record055_frame012_links
def record055_frame013_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0301.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0301.count (({ width := 8, code := 0xa7a6a5a4a29e9b9998979592918f8e8d8c8b8988878684807d7b7a7977747371706f6e6d6b6a69686463625e5d5b57565453514e4c4a4948474543403e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161211100e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0301.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0301.localPairCheck (smallEmbedding record055) (record055.maps 13) (record055.inverseMaps 13) record055_frame013_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0301.localPairCheck (smallEmbedding record055) (record055.maps 13) (record055.inverseMaps 13) record055_frame013_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0301.localPairCheck (smallEmbedding record055) (record055.maps 13)
      (record055.inverseMaps 13) record055_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame013_links_0000 record055_frame013_links_0064)
theorem record055_frame013_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 13 :=
  of_group record055 13 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0301
    Papers.RationalityTen.SharedFrameCatalogue.group0301_facts record055_frame013_indices record055_frame013_graph record055_frame013_links
def record055_frame014_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0187.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0187.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0187.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0187.localPairCheck (smallEmbedding record055) (record055.maps 14) (record055.inverseMaps 14) record055_frame014_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0187.localPairCheck (smallEmbedding record055) (record055.maps 14) (record055.inverseMaps 14) record055_frame014_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0187.localPairCheck (smallEmbedding record055) (record055.maps 14)
      (record055.inverseMaps 14) record055_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame014_links_0000 record055_frame014_links_0064)
theorem record055_frame014_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 14 :=
  of_group record055 14 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0187
    Papers.RationalityTen.SharedFrameCatalogue.group0187_facts record055_frame014_indices record055_frame014_graph record055_frame014_links
def record055_frame015_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0180.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0180.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0180.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0180.localPairCheck (smallEmbedding record055) (record055.maps 15) (record055.inverseMaps 15) record055_frame015_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0180.localPairCheck (smallEmbedding record055) (record055.maps 15) (record055.inverseMaps 15) record055_frame015_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0180.localPairCheck (smallEmbedding record055) (record055.maps 15)
      (record055.inverseMaps 15) record055_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame015_links_0000 record055_frame015_links_0064)
theorem record055_frame015_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 15 :=
  of_group record055 15 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0180
    Papers.RationalityTen.SharedFrameCatalogue.group0180_facts record055_frame015_indices record055_frame015_graph record055_frame015_links
def record055_frame016_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0175.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0175.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0175.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0175.localPairCheck (smallEmbedding record055) (record055.maps 16) (record055.inverseMaps 16) record055_frame016_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0175.localPairCheck (smallEmbedding record055) (record055.maps 16) (record055.inverseMaps 16) record055_frame016_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0175.localPairCheck (smallEmbedding record055) (record055.maps 16)
      (record055.inverseMaps 16) record055_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame016_links_0000 record055_frame016_links_0064)
theorem record055_frame016_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 16 :=
  of_group record055 16 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0175
    Papers.RationalityTen.SharedFrameCatalogue.group0175_facts record055_frame016_indices record055_frame016_graph record055_frame016_links
def record055_frame017_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x342d9ecce0665301d654a8951aa88d42099147d234515889a41820710187e93eb1f1cf6e6d32fb1554a024ef26e117478c39d1bc0d985f82e816c0ad454429314188e446422b10787e83e61d60e807083681a60cb86282f61750a9051027a13509084642180f607802c813a09204682300f607a03881bc0da06a03481840c005d02d81680ae05602a815008604201c80dc06a03201880a4050025011808803e01e00e807002a014009804402000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record055_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record055) (record055.maps 17) (record055.inverseMaps 17) record055_frame017_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record055) (record055.maps 17) (record055.inverseMaps 17) record055_frame017_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record055) (record055.maps 17)
      (record055.inverseMaps 17) record055_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame017_links_0000 record055_frame017_links_0064)
theorem record055_frame017_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 17 :=
  of_group record055 17 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record055_frame017_indices record055_frame017_graph record055_frame017_links
def record055_frame018_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x11ee3bc738dd13e10bf87c4f81ee3b9726e1dc037c6c2d69aab4d68acfd9db105beae151aa053a9d9292484808f51121b42a829019fe3f4754e61c435865cc797b2ea59cab9492724a48b9101e43a0720de19a3185d8ac1502204207f0f61e83806f0d0198320610c01602b8540a41442704d09812c208400720dc1a8320620a4140250460880f81e03a0700a8140260440800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record055_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record055) (record055.maps 18) (record055.inverseMaps 18) record055_frame018_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record055) (record055.maps 18) (record055.inverseMaps 18) record055_frame018_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record055) (record055.maps 18)
      (record055.inverseMaps 18) record055_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame018_links_0000 record055_frame018_links_0064)
theorem record055_frame018_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 18 :=
  of_group record055 18 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record055_frame018_indices record055_frame018_graph record055_frame018_links
def record055_frame019_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x106e0b41181cfdde93ad734e4dc7b786aed299fb3c63cc55883035f8be178ad0552a193926d4d094515a1e422830f99ea3c8770ea9cf3946c4d59a5320608bd95e2b0534a193524e4648890c1ec3b4730e019a3145d8a814820c3e87a0ee1d83606b0ca18c3085e0ba1582a8520a013c2604b0941241f83e06e0d81a0310600a4140250460880f81e03a0700a8140260440800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record055_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record055) (record055.maps 19) (record055.inverseMaps 19) record055_frame019_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record055) (record055.maps 19) (record055.inverseMaps 19) record055_frame019_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record055) (record055.maps 19)
      (record055.inverseMaps 19) record055_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame019_links_0000 record055_frame019_links_0064)
theorem record055_frame019_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 19 :=
  of_group record055 19 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record055_frame019_indices record055_frame019_graph record055_frame019_links
def record055_frame020_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0764.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0764.count (({ width := 8, code := 0x91908f8e8c8a888786858483817f7e7d7b7a78767574716f6d6c6b6a696866646362605f5d5b5a595756555453524f4e4d4c4b494745444241403f3e3d3c3a39363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record055_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0764.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0764.localPairCheck (smallEmbedding record055) (record055.maps 20) (record055.inverseMaps 20) record055_frame020_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0764.localPairCheck (smallEmbedding record055) (record055.maps 20) (record055.inverseMaps 20) record055_frame020_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0764.localPairCheck (smallEmbedding record055) (record055.maps 20)
      (record055.inverseMaps 20) record055_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame020_links_0000 record055_frame020_links_0064)
theorem record055_frame020_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 20 :=
  of_group record055 20 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0764
    Papers.RationalityTen.SharedFrameCatalogue.group0764_facts record055_frame020_indices record055_frame020_graph record055_frame020_links
def record055_frame021_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0738.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0738.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0738.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0738.localPairCheck (smallEmbedding record055) (record055.maps 21) (record055.inverseMaps 21) record055_frame021_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0738.localPairCheck (smallEmbedding record055) (record055.maps 21) (record055.inverseMaps 21) record055_frame021_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0738.localPairCheck (smallEmbedding record055) (record055.maps 21)
      (record055.inverseMaps 21) record055_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame021_links_0000 record055_frame021_links_0064)
theorem record055_frame021_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 21 :=
  of_group record055 21 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0738
    Papers.RationalityTen.SharedFrameCatalogue.group0738_facts record055_frame021_indices record055_frame021_graph record055_frame021_links
def record055_frame022_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x12924ec9992b21a3143c84106e09bed77eeb1cd3906d2d85ac34b688cf99d3235f4b3154aa152e9dd282414688b1031fd3ea7a0f01db3ae6ecdb9b1344654c797a2f05b0b01542864d8939212043d4780e71a43285e8aa148234438800f61e83806f0ce194318610c01602b8540a41442704d09812c2084006e0d41983005e0a0138250460880f81e03a0700a8140260440800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record055_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record055) (record055.maps 22) (record055.inverseMaps 22) record055_frame022_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record055) (record055.maps 22) (record055.inverseMaps 22) record055_frame022_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record055) (record055.maps 22)
      (record055.inverseMaps 22) record055_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame022_links_0000 record055_frame022_links_0064)
theorem record055_frame022_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 22 :=
  of_group record055 22 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record055_frame022_indices record055_frame022_graph record055_frame022_links
def record055_frame023_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x78b78377c7727366f36be69368d68364e6025e85d15c458557d57356355654c5404ec49844d42041440a3d63a539238037a33b32e32430b3002fb2f12b12a729927224f2472202182071f11dd1c81ba1a219816415214713d11a10d0fd0e30dc0a409508c08708607707606e06c06a06706605e05d05a05805705405305205104204103803603403103002902802502302201f01e01d01c01501401301101000e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record055_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record055) (record055.maps 23) (record055.inverseMaps 23) record055_frame023_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record055) (record055.maps 23) (record055.inverseMaps 23) record055_frame023_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record055) (record055.maps 23)
      (record055.inverseMaps 23) record055_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame023_links_0000 record055_frame023_links_0064)
theorem record055_frame023_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 23 :=
  of_group record055 23 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record055_frame023_indices record055_frame023_graph record055_frame023_links
def record055_frame024_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0415.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0415.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0415.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0415.localPairCheck (smallEmbedding record055) (record055.maps 24) (record055.inverseMaps 24) record055_frame024_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0415.localPairCheck (smallEmbedding record055) (record055.maps 24) (record055.inverseMaps 24) record055_frame024_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0415.localPairCheck (smallEmbedding record055) (record055.maps 24)
      (record055.inverseMaps 24) record055_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame024_links_0000 record055_frame024_links_0064)
theorem record055_frame024_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 24 :=
  of_group record055 24 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0415
    Papers.RationalityTen.SharedFrameCatalogue.group0415_facts record055_frame024_indices record055_frame024_graph record055_frame024_links
def record055_frame025_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0392.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0392.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0392.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0392.localPairCheck (smallEmbedding record055) (record055.maps 25) (record055.inverseMaps 25) record055_frame025_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0392.localPairCheck (smallEmbedding record055) (record055.maps 25) (record055.inverseMaps 25) record055_frame025_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0392.localPairCheck (smallEmbedding record055) (record055.maps 25)
      (record055.inverseMaps 25) record055_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame025_links_0000 record055_frame025_links_0064)
theorem record055_frame025_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 25 :=
  of_group record055 25 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0392
    Papers.RationalityTen.SharedFrameCatalogue.group0392_facts record055_frame025_indices record055_frame025_graph record055_frame025_links
def record055_frame026_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0186.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0186.count (({ width := 7, code := 0x1dbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record055_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0186.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0186.localPairCheck (smallEmbedding record055) (record055.maps 26) (record055.inverseMaps 26) record055_frame026_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0186.localPairCheck (smallEmbedding record055) (record055.maps 26) (record055.inverseMaps 26) record055_frame026_indices (Fin.ofNat record055.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record055_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0186.localPairCheck (smallEmbedding record055) (record055.maps 26)
      (record055.inverseMaps 26) record055_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record055_frame026_links_0000 record055_frame026_links_0064)
theorem record055_frame026_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 26 :=
  of_group record055 26 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0186
    Papers.RationalityTen.SharedFrameCatalogue.group0186_facts record055_frame026_indices record055_frame026_graph record055_frame026_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (Fin.cases (record055_frame002_supported hcells) (Fin.cases (record055_frame003_supported hcells) (Fin.cases (record055_frame004_supported hcells) (Fin.cases (record055_frame005_supported hcells) (Fin.cases (record055_frame006_supported hcells) (Fin.cases (record055_frame007_supported hcells) (Fin.cases (record055_frame008_supported hcells) (Fin.cases (record055_frame009_supported hcells) (Fin.cases (record055_frame010_supported hcells) (Fin.cases (record055_frame011_supported hcells) (Fin.cases (record055_frame012_supported hcells) (Fin.cases (record055_frame013_supported hcells) (Fin.cases (record055_frame014_supported hcells) (Fin.cases (record055_frame015_supported hcells) (Fin.cases (record055_frame016_supported hcells) (Fin.cases (record055_frame017_supported hcells) (Fin.cases (record055_frame018_supported hcells) (Fin.cases (record055_frame019_supported hcells) (Fin.cases (record055_frame020_supported hcells) (Fin.cases (record055_frame021_supported hcells) (Fin.cases (record055_frame022_supported hcells) (Fin.cases (record055_frame023_supported hcells) (Fin.cases (record055_frame024_supported hcells) (Fin.cases (record055_frame025_supported hcells) (Fin.cases (record055_frame026_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd286642c09562a8952fa92d41c96b48f23e91ce8bf44c20c103880c3fd9f58f8e7952e715f4aaa52b28b936886e3ea1e30ecc71636417e0ba05b02c71510a4c4c2239112087441e20810087e83e61ec0f1877039c1c20da069832e1910bd859c2a414409e84d425011907f03d81e009104702340e206e03681ac0d406102f81740b805b02b81580aa05401c80d806a03301900a404e025012008c03e01e00e807002a014009004402000f0070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
def record056_frame002_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65f6485ea5c95bd5ab59d57c54652751850c4f64dd4bb4b44ae4a949b4954834133f23e63d43c83a336934c33c33131d3002e02d82d22cd2c02bb2ae28926925c24924023322721d2132061f91e21d51c41b119819117215513e12c1211141010ec0c50bc0b808508408306e06b06a06806705f05d05b05a05905505405305203803503403203102902702502402301f01e01d01c01501401201101000f00e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record056_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record056_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record056) (record056.maps 2)
      (record056.inverseMaps 2) record056_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record056_frame002_links_0000 record056_frame002_links_0064)
theorem record056_frame002_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 2 :=
  of_group record056 2 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record056_frame002_indices record056_frame002_graph record056_frame002_links
def record056_frame003_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x4ad9271622243c8630a608be4794efddbba171cda5b0b586a4d119f3315e0b59662be564a5536a5a4a09291d22a40c7f4fa9ef3c076ce71bb35c6acd119f334654c798a3065f4bb16c2c0550a193d24e458810f51e039c6c8ca1642a85207f0f81ec338640c6188308580ac1502985209c1342604b06e0d0198310600a01302504808c0f81e03a0700a8140240440800f01c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record056_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record056) (record056.maps 3) (record056.inverseMaps 3) record056_frame003_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record056) (record056.maps 3) (record056.inverseMaps 3) record056_frame003_indices (Fin.ofNat record056.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record056_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record056) (record056.maps 3)
      (record056.inverseMaps 3) record056_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record056_frame003_links_0000 record056_frame003_links_0064)
theorem record056_frame003_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 3 :=
  of_group record056 3 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record056_frame003_indices record056_frame003_graph record056_frame003_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (Fin.cases (record056_frame002_supported hcells) (Fin.cases (record056_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x344d91ac3a55728a13aa9ae4cca6492fa96f4b0a561286930491246d22690647ba3c51b872234b18fcbc65ac2cc9584a7a518281933c93447723391508644112010f446e833d1950bc859c2a914a09804562080fc07943861a20c985882ac14f0a4050427413308f04281ec0ef049824411c08d03801b80d606a03101840be05e02e016c0b005702b01540a803801b00cc06402a014809c04c024011808003e01e00e807002a014009004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
def record057_frame002_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x372da50cc8577a97d41c9b64bf25ad26490c473a34913086442120c103c7fb3ec1f20f2a5bb295936890444a21b8ff87b03b31cf0d9066030e17e0ba858e2a414a098447222410e88203f41ec0f187383761ad0d306783221820be059c2c01590a9052c28813d094044c1fc0f7049824411c08d03801b80d606a03101840be05e02e016c0b005702b01540a803801b00cc06402a014809c04c024011808003e01e00e807002a014009004401e00e0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record057_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record057_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record057) (record057.maps 2)
      (record057.inverseMaps 2) record057_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record057_frame002_links_0000 record057_frame002_links_0064)
theorem record057_frame002_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 2 :=
  of_group record057 2 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record057_frame002_indices record057_frame002_graph record057_frame002_links
def record057_frame003_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xe05abb3a5c8ae94ea8d508a053c2724d899d2f2574a29392524547c8f1199de36865cc397e2f65c8b61662c2560a894b2905109f93826c4b48f115224424818fd1f03bc740e21be36c6b0cf19a310608c017e2f85e8bc1722d8598b211e234450890dc1b0348680c017c2e85c0b41642b0550a814c2903806c0cc1902a05209c130240460800f81e03a0700a8140240440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record057_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record057_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record057) (record057.maps 3)
      (record057.inverseMaps 3) record057_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record057_frame003_links_0000 record057_frame003_links_0064)
theorem record057_frame003_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 3 :=
  of_group record057 3 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record057_frame003_indices record057_frame003_graph record057_frame003_links
def record057_frame004_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x1892fede7b0d55ea0d24a1d40a75cda98b2f6554949011d234c5787f0de0cbb1704db1a7b3c662c71872fa5e6ba168abd566aa54ea8a5089bd2623945c859049f63d8774e29b335067cc89802f2588ac9502945089992721c3cc6d8d11022003f07d0d019c328640b816c2c8580ac154290510a013c2703806c0cc1902a05209c130240460800f81e03a0700a8140240440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record057_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record057) (record057.maps 4) (record057.inverseMaps 4) record057_frame004_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record057) (record057.maps 4) (record057.inverseMaps 4) record057_frame004_indices (Fin.ofNat record057.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record057_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record057) (record057.maps 4)
      (record057.inverseMaps 4) record057_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record057_frame004_links_0000 record057_frame004_links_0064)
theorem record057_frame004_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 4 :=
  of_group record057 4 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record057_frame004_indices record057_frame004_graph record057_frame004_links
def record057_frame005_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x122a3745780efb1eabbe768eadcdb9370adf9b635c6a6d31a2b36650c8186ab65269fd3425c4ae9251e22d44a859031fc3ea7bcf31d73a4704d4198320604bc16e2ce560a413d2724bc9211522040c7e8f71e43bc740e11a42fc578aa0fa1f03c8780d61a4338660bc1742e05b0b41642b0550a814c2903806c0cc1902a05209c130240460800f81e03a0700a8140240440780e0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record057_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record057) (record057.maps 5) (record057.inverseMaps 5) record057_frame005_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record057) (record057.maps 5) (record057.inverseMaps 5) record057_frame005_indices (Fin.ofNat record057.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record057_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record057) (record057.maps 5)
      (record057.inverseMaps 5) record057_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record057_frame005_links_0000 record057_frame005_links_0064)
theorem record057_frame005_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 5 :=
  of_group record057 5 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record057_frame005_indices record057_frame005_graph record057_frame005_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (Fin.cases (record057_frame002_supported hcells) (Fin.cases (record057_frame003_supported hcells) (Fin.cases (record057_frame004_supported hcells) (Fin.cases (record057_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x191ac38514274d35c9994c925852b29524a624f926e930494a489236912485a3f51f08f146d9a58c7a5e32d61664a30504279938497c4ac24d12208ee46722991048424122010f406e833d1950aa452a284139093c47a22b10c88203f01e40e906c83461930b0855829e1480a084e826611e08804281ae09b04702340f006b03501880c205f02e016c0b405902c015c0ac05402000cc06402a014809c048023011008404001f00f007002a014009003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
def record058_frame002_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a50cc652fa83136c97e4b5a39d1a68c0456a2210ec864429210906081d4059f9cfb27c83ca14ac9b048222510dc76639f1c60de46a83421980c7861c2fc1748b5c5662a514a098047222410e87b03c81dd0eb87243841bb0da06b434c19d0cb062030617c0b305802b21520a5851027a12808d044c1b609b04702340f006b03501880c205f02e016c0b405902c015c0ac05402000cc06402a014809c048023011008404001f00f007002a014009003c01c00d006002c014009003801800a0040018008002000 } : Fields).get c.val)
theorem record058_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record058) (record058.maps 2) (record058.inverseMaps 2) record058_frame002_indices (Fin.ofNat record058.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record058_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record058) (record058.maps 2)
      (record058.inverseMaps 2) record058_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record058_frame002_links_0000 record058_frame002_links_0064)
theorem record058_frame002_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 2 :=
  of_group record058 2 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record058_frame002_indices record058_frame002_graph record058_frame002_links
def record058_frame003_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1abb38574a6d46a845029b1342654c69752d2574a89452724948c9011fa3c4646d0ca9872fc5ecb31622be574ab9542a2538a59482865009d13926c4b08f1152243f47c8f61e83b8758e81ca3886f8da1ae344680cd186304600bf17c2f45e0b916e2d8570971142243b0690d01802f85d0b41642c0570ac1542a0520800cc1902a05209c120230440841001f03c0700a81402403c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record058_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record058) (record058.maps 3) (record058.inverseMaps 3) record058_frame003_indices (Fin.ofNat record058.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record058_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record058) (record058.maps 3)
      (record058.inverseMaps 3) record058_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record058_frame003_links_0000 record058_frame003_links_0064)
theorem record058_frame003_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 3 :=
  of_group record058 3 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record058_frame003_indices record058_frame003_graph record058_frame003_links
def record058_frame004_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa4ea089038c089386c85d7f77df7ce7bf79b79078076f7607507397256fe6ed6db6a159d55e53e51f5124bd4ab49d49047546d4604524444364234133f33e63d83a73793523452e72d82cc2be2a029628627526725a2472372182091fa1cc1c21ba1ae1a019118315613712b0c009508808707606906806005f05d05a05905805705605505405204003303202a02902702402302202102001f01e01c01501401200f00e00d00c00b00a009007006005004003002001000 } : Fields).get c.val)
theorem record058_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record058) (record058.maps 4) (record058.inverseMaps 4) record058_frame004_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record058) (record058.maps 4) (record058.inverseMaps 4) record058_frame004_indices (Fin.ofNat record058.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record058_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record058) (record058.maps 4)
      (record058.inverseMaps 4) record058_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record058_frame004_links_0000 record058_frame004_links_0064)
theorem record058_frame004_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 4 :=
  of_group record058 4 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record058_frame004_indices record058_frame004_graph record058_frame004_links
def record058_frame005_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2b7d4999128a474818f915a274478850d617c2884506e0a40b808fd9f83e77a4ce1862f75c8b7156aa453aa5d442814f29c9352624ae93d1fa3745c848fe1eb3ca6c8d49a2338634c397f2ee5c0b395d2aa5109e13322e444869082043f47c0e71b8358558870fa1f0370640c61702d8590ac1542a0530a41442804e0800cc1902a05209c120230440841001f03c0700a81402403c0700d01802c0500900e0180280400600800800 } : Fields).get c.val)
theorem record058_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record058) (record058.maps 5) (record058.inverseMaps 5) record058_frame005_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record058) (record058.maps 5) (record058.inverseMaps 5) record058_frame005_indices (Fin.ofNat record058.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record058_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record058) (record058.maps 5)
      (record058.inverseMaps 5) record058_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record058_frame005_links_0000 record058_frame005_links_0064)
theorem record058_frame005_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 5 :=
  of_group record058 5 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record058_frame005_indices record058_frame005_graph record058_frame005_links
def record058_frame006_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0658.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0658.count (({ width := 9, code := 0x31d81b5d7ab557ab5268d43a0cfa7b3b9ccda673096caa53268e419f2f5793c5c8e16f371b2d86b351a2ce65b218ac460add66b057a893e9c4d25d2c944923d18894320d047f3a9cce471381bcdc6b349a0c05d2b958a84e269188a43200fc7c3d1e0ec74381b8c46029140984622108803e1e0e86c2a140903c1c0d0602c1409038180a04018080200 } : Fields).get c.val)
theorem record058_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record058) (record058.maps 6) (record058.inverseMaps 6) record058_frame006_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record058) (record058.maps 6) (record058.inverseMaps 6) record058_frame006_indices (Fin.ofNat record058.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record058_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0658.localPairCheck (smallEmbedding record058) (record058.maps 6)
      (record058.inverseMaps 6) record058_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record058_frame006_links_0000 record058_frame006_links_0064)
theorem record058_frame006_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 6 :=
  of_group record058 6 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0658
    Papers.RationalityTen.SharedFrameCatalogue.group0658_facts record058_frame006_indices record058_frame006_graph record058_frame006_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (Fin.cases (record058_frame002_supported hcells) (Fin.cases (record058_frame003_supported hcells) (Fin.cases (record058_frame004_supported hcells) (Fin.cases (record058_frame005_supported hcells) (Fin.cases (record058_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record058_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012
