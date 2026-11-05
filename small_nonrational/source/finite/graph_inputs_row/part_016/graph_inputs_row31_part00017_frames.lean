module
prelude
public import GraphInputsRow31Part00017Data
public import RawFrameSupport
public import SharedFrameGroups019Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups065Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xccf92b14de5b6f63aaed42a7d4c2885089ef3766bcc597b2c64ac878e115e27c3e84b079fdbc773ad3da4b42656c858c308608bbd732cc584ad14d2914b494d23a2c43e844ff1f83bc74cda1aa3325ecb91572985049e93224a4588990a1f63dc750e61ae348678c51622904e89611e238438820fe1f83e86e0ce1903184f07c0d4190310600bc1702a04e0941182203e0780e81c0360680c8150240400700d01402404007 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x73c7026d868763e60a5dc5c65bc5aa58457055b5485365125084fc4e04d44b849e49548f48447d45a4173e639e39238336335734833532d3083022ed2e02cf2b82b42842782662442382262112091e31dd1c41b61a518b18716e16315e15814913d1291221161020fd0f00ec0e00d40cf0c60bb0b20a60a109409308b08508108007f06f06806406304f03e03603203103002f02e02a02702502302201f01e01d01c01b01a01901501201000e00d00a009008007 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0357.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0357.count (({ width := 8, code := 0xe8e5e2dedbd8d4d0cfcdcccbc9c8c6c4c3c2c0bfbdbbbab8b6b5b4b1aea5a4a39e9d9b97969493908d8c8a8981807f7a79777372706f6c69686665615e5b5a58565453514e4d4b4a47464543413f3e3d3c3b3a39383736353433322b282625242322211d1c1b1a19181716151413120e0d0c0b0a09080706 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0357.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0357.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0357.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0357.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0357
    Papers.RationalityTen.SharedFrameCatalogue.group0357_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x7033541996ba1575a99938e9b14d5266930c9794b4a5712a894249ca4c9238916483a3f11e68eb470236506276236a9784ba05ac2b99534a5650427a12ac93246722a10c88023f11b90d8467a30416f0af052a28511e08a83f01e50e186483041550a7051c28413b09a04ac24c11f08b044421210507e03d41e00ea07103701ac0d005782b8136091046823011607803701a80d205302000d806403101800bc05c02a013809404602200f807803a01c00d8068032015009004001c00d0050024010007 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x9251de3042d826fe1e8bc0778ecdd039a71ee01be3716d8d9dabb52686cd19732462ac457d2d155a9bd362674ac9311fa3345c8750ba043fc7d0ee9d7358698ce1883045ecb796d2b6558a113a25c458888fc1f03d0788ea1c83786e8d719c334628c31742d85a0af14e2884e0971222404287f0f61e83c86e0ce1903184f0800d8190310600bc1702a04e0941182203e0780e81c0360680c8150240400700d01402404007 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0xba3672b6d209cb2ea44c7e8f11b62dc4b87b0ca14c13815005f73e87b0f25e13bb766ebdcab5f664bb1722d757cacd5529a52c9c9362584988f511a1e3e27acee1bf362690c898a2cc588aa14927c4989110e20e408800fa1ea3b4748e21b2354668cc1862f05c0b31542984f89a11a2304107d0f41e43c06f0d2198328510800d8190310600bc1702a04e0941182203e0780e81c0360680c8150240400700d01402404007 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
def record001_frame007_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0437.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0437.count (({ width := 7, code := 0xefdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0437.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0437.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0437.localPairCheck (smallEmbedding record001) (record001.maps 7) (record001.inverseMaps 7) record001_frame007_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0437.localPairCheck (smallEmbedding record001) (record001.maps 7)
      (record001.inverseMaps 7) record001_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame007_links_0000 record001_frame007_links_0064)
theorem record001_frame007_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 7 :=
  of_group record001 7 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0437
    Papers.RationalityTen.SharedFrameCatalogue.group0437_facts record001_frame007_indices record001_frame007_graph record001_frame007_links
def record001_frame008_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0297.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0297.count (({ width := 7, code := 0xefdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0297.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0297.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0297.localPairCheck (smallEmbedding record001) (record001.maps 8) (record001.inverseMaps 8) record001_frame008_indices (Fin.ofNat record001.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record001_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0297.localPairCheck (smallEmbedding record001) (record001.maps 8)
      (record001.inverseMaps 8) record001_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record001_frame008_links_0000 record001_frame008_links_0064)
theorem record001_frame008_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 8 :=
  of_group record001 8 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0297
    Papers.RationalityTen.SharedFrameCatalogue.group0297_facts record001_frame008_indices record001_frame008_graph record001_frame008_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (Fin.cases (record001_frame007_supported hcells) (Fin.cases (record001_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6b93025658a9f4fd26e134891c47d23050c68303fd9f1cf6e6d52fc15ac98c4842380fa078c38d1978bf058e29314188dc46022410707fc3e61e40ef07043741a60cf06442f61750af856028813d09a84bc25010c07802bc136091046823011607803701a80d206602f81740b605a02b81580aa054029810006c03201880b804e025011808803e01e00e807003601a00c80540240100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6d868763e60a5dd5c05b656c5555304f84da4b249348d45a4173e63bc3a239635734832d3022ed2cf2b82b42842782662442382262112091e31dd1c41b61a518b18717116614613a12d11f1130eb0c509408b08508108007f06f06806406306005b05905705605305205105004f03e03603203102e02702502302201f01e01d01c01b01a01901501201000e00d00a009008007005004003002001000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1946c7654327f93b29c04d7a67525c91c48323f11d487b434a14d09282e4079e38efc6e436a199cca45be2d01630aee56a2a89464a164f8275137498848c23f11ac8a043f1ca8df86de36117e8bb459c2c012e09304602030f786dc34417a0b4055428a13c098845c2100ff07a036815e0ae048023410a07803701a80d206602d81580a8053026810006c03501900c406002f017009804602100f0070032014009804801c00d004802000e005002000c002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb12aad93f9088e78d78c78b584c83882081480479778276a7536fb6ec6c06b266c65f6085e257656055353e52e51c4e24d44c04b14a249045a44b4393ed3e338837b36d35a2f92e92c92b92642542311df1d21b51a81851761691541451351141010f70ea0cc0a80a709008d08507806e06a06906605b05605405304d04003603503203103002f02e02602302101e01c01901401301200e00d009008007005004003001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2ec962ca9f51aa7e536e9934a3a48117c8754181fecf6e67e2f115aca024c5241917c8263ec1c50d045f82c714188e045221d10707fc3e61c10dd069832e1910bd85d42bc1510a584f426c12e094046822410c07b82bc136091046823011607a03c01b80d4069033817c0b605a02b81580aa054029810808003601900c405e027011808803e01e00e807003601a00c80500240100070034014009004001c00c0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0xa574827fcaf9431fa35c4987d0a5fa3e37b4f55e83b0724d419eb29628c017e2d6590ad155a844d89792924c4929151822b43283cff1db3986c0cc98b30c5e0bb16f2c64d49711a2224347b8e61c02d8590ac1202244007d0f81c0350690ca1902e05a0b21602a0530a41441f03d06e0d41883005e09c120230440840f01d0380640a01201e0380680b0120200380400600800800 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7397096d669969568f68367765f65263061b5e05a259559458b57956f55a5475454f14ea4e74de4bf49348c48847845942441d4124053f93e23a736936435534a34032b32130e30c2b82b62aa29c27a25a2582472352111ee1df1d91cc1c01bc18c18417e17116115815114c13d12d12612011611110e10d10b1060d70d10ce0bd0b70b40a90a109d09008b08a08307607006e06705805705405305204f04e04503f03c03602702502302202001e01d01200f00e00d00a009008003002001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0xcdb90b0a5d1b9f726e1dbcb5d696c7d7aa9944a81d019f73c2734d798f3164c49191d2263c45c8ad1522743c84106e0ac0d80ef91d4b636b0d2da0b39652c818830f582afd5b2a85189bd372664b691117a2544286109a103926f0db9a230c5e0b51672ae4f4981282404648a1102144106a0d01962e45b0b214a2744d88f11021c408740dc1b43385f0bc16c2d0590ac1542384007a0d8138250460881001e03a0480780e01a0280480800600800800 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0xc661b0379bc5dae972b7db6d165b056aad55a9d429d4aa3d1a7d3c9dce6672b94ca24d208b456250d85c2206fd7dbddeaf377bb5d4e970b81bada6a3399aca63b0172b65aac15cad5328d429c4b24d208e44a04fa7a3b9d0e471379b4bc5d2e164b0572a14ca44f271349444219087e391c0d46833180bc562a14898401e0e06c32170b0481e0e068281208018080200 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x67db279898be45f02f25762ba05beadb169ab0e555295d464a2950927c53c49c14d9a6bd254914483a3b116a86e42ca1390647fe3df1ec0f2877d3b59c80d5664e31c9854bfe5ef2e91708b685b129a94bca1c4f4264927c93447d23210f083c4071fc8f9c7b63d01ac0cd06422f71650ae052e28713008e84522150ff87c83ca1dc0e506dc2a2141098040c1f00ea06402f01700a404d826812208003c01d80dc05f02f016c0b405902b015408e04001e80d804e025011808804001e00e804801e00e00680280120080018008002000 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0xab34e68ecfb9f33d678ceb9c137666cb993b2023bc758e119230c5889b12a0a40d81500df63ce78cf11deba671ce25c0b776ded4d9c31461ac0d7d2f45d6b996eadb544a7d4a28b4ec9712d24e48a8bd0ea1241a810fd9f63866d0d79993125f8b71692a850c9c12f2484748a910212408690cd18e2d0578a913224c490871042043e0710da1b03385b0b415c2b0550a41442284007a0d8138250460881001e03a0480780e01a0280480800600800800 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x7293779a8acb6659b2b1948c9d647b2218f0c155b9ab755a6acf563aae5564aa454daa5d3469944c6a5d92808f0470a36918688d425a11907c8364179f14e3667d33b19b4cc265a3261914c7a63a2ba15ccab654328c139c9cc4ce25b122c8ce46022e11588a24491b98d6869831f1770b485722ab13f093446622b111887042a20c0fb878828613909804181f80f306903281820a404d826812208003c01d80dc05f02f016c0b405902b015408e04001e80d804e025011808804001e00e804801e00e00680280120080018008002000 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
def record008_frame007_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0xc0d77ad7d76ae95c2b3d60aad53ea1d2d9eb3265f4bd9692a651c9792122e2ac4c89310617c0c808ffdfbbe578cf05dd3b4760e75b5b3f672cc194b24632c4d86309578aed592aa52c9e53ba6b4bc91514a2243e8650920e3886d4d819d3005bcb21612a84f8971282424788b912216410688cf1922d0578ac136258498871042043e8720de1b83485d0b81642c0570a814c2384007a0d8138250460881001e03a0480780e01a0280480800600800800 } : Fields).get c.val)
theorem record008_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 7) (record008.inverseMaps 7) record008_frame007_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 7)
      (record008.inverseMaps 7) record008_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame007_links_0000 record008_frame007_links_0064)
theorem record008_frame007_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 7 :=
  of_group record008 7 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record008_frame007_indices record008_frame007_graph record008_frame007_links
def record008_frame008_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0372.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0372.count (({ width := 8, code := 0xfcfaf5efeeedeceae8e7e6e4dfdad8d7d6d4d2d1d0cfcac9c8c7c3bebdbcbbb7b2b1afadacaaa5a09f9d9c9a98979695908f8e8c88848382807c7876757372716c6b6a6763605f5e5b575452504f4e4d4c4b4342413e3d3c393837363534332f2e2d2c262524232221201e1d1c1b1514131211100f0b0a090807060503020100 } : Fields).get c.val)
theorem record008_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0372.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record008) (record008.maps 8) (record008.inverseMaps 8) record008_frame008_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0372.localPairCheck (smallEmbedding record008) (record008.maps 8)
      (record008.inverseMaps 8) record008_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame008_links_0000 record008_frame008_links_0064)
theorem record008_frame008_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 8 :=
  of_group record008 8 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0372
    Papers.RationalityTen.SharedFrameCatalogue.group0372_facts record008_frame008_indices record008_frame008_graph record008_frame008_links
def record008_frame009_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x71a6ee6bf69168e68767f67b67066c6606325ef5b55aa5a659e59558f58657f57d52f52351f5134f44d84cc4c84bb4a648648147947046b4383ec3aa3a539d39439038638237b37a32832731630c2f72e42e32d22c82b52a72a029c2962932902292142091f31dc1d11bc1b119e18617b17316b16516115d1521470f60ef0e60d00c90c00b00a90a509609109008b07a07407206c05d05c05905805705405304503f03c03602702502302202001e01d01200f00e00d00a009008003002001000 } : Fields).get c.val)
theorem record008_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 9) (record008.inverseMaps 9) record008_frame009_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record008) (record008.maps 9)
      (record008.inverseMaps 9) record008_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame009_links_0000 record008_frame009_links_0064)
theorem record008_frame009_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 9 :=
  of_group record008 9 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record008_frame009_indices record008_frame009_graph record008_frame009_links
def record008_frame010_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x8790ba0e409811011ffbfa7e4fb9f03d0768e55c638b70edf5bcb6f6ccd919fb3a672cd994314622c4183afa5c8b896ead459caf54f2834fc9d93826b4c89752a2524588ad112194167f0fd9f43d8788ea1cc396704de1ba3105f8bd96d2b653ca51422644888b11121640c7d8f81e83b8628bf1782a4528a011c230448820fe1f83d86d0d019c308540a61402784e0961281f83a0720d0138250460881001e03a0480780e01a0280480800600800800 } : Fields).get c.val)
theorem record008_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 10) (record008.inverseMaps 10) record008_frame010_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record008) (record008.maps 10)
      (record008.inverseMaps 10) record008_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record008_frame010_links_0000 record008_frame010_links_0064)
theorem record008_frame010_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 10 :=
  of_group record008 10 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record008_frame010_indices record008_frame010_graph record008_frame010_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (Fin.cases (record008_frame007_supported hcells) (Fin.cases (record008_frame008_supported hcells) (Fin.cases (record008_frame009_supported hcells) (Fin.cases (record008_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x2efdb9b2960ab4548a7144a76cd49772864f4728db1a21b42d84d051ffbf17d0f5de8bbc6bed35a1b3164cc2d83ace58cb115f2a550e9d9392624b29211aa2f432845061d33a071cdd9a3318610b81672ae5349e93123c4588910c20e3e0738db1aa340600bb14c26c438851001b8360670b21542a0510a013c268470800fc1f03d06c0bc138260460881081f03c0740c8120200380680b0140240400400600800800 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x195cc4d5f92ec56fab4d58faaad4aaa024e926cd35693648ea4050f8857421a03cfb67c43d69df4ed672131f9838bfe5e12e916d0b465372929450a044d725091f88e245722490bc82e40b1f38f6c78c34d19e0c8860c2d91570a684da26012388e844c2110f907943b01c30da06402da1540a184c420c0fa06402e013609904881e00ea06e02f816c0b405702b01540a604902000fc07c03d01b00bc04e026011808804201f00f0074032012008003801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x205bfe7daf81e83bb772eb1cdb896f8da5b3347684cf1863045fabbd6f2d459ab015d2b25089ed39a694ca94d27a3545e8ad13a133f47b0f59e03b4734df1bb35668ccd9812fa5d4b415828c4fc97127240464879021ec3b8740e21b83345f8b515e2ac4c09410c2083b0750e01943205f0a613c2704b094124238450800fc1f03d06c0bc138260460881081f03c0740c8120200380680b0140240400400600800800 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf4873f33158a2b8654629414169fa4a1a4d12388fa460a2290e68634181fecfb67a53c99c74ca455828e135c98c40f2000fa078c38d1ab0cfc65e2fc1638a9c4e225f10307fc3f41f30f2877838e1ba0da069833e1910c085b02ca15f0ac051027a12f09404642180f6078035413609104582040f007603701980be05d02d81680ae05602a814c09204001f00d805c027012808c04401f00f007403601a00c8048022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x74d7166b26996556055f65e45dd57c57456c55553050d5004f84da4b249b48748046942b3e13d43c23bc36235d35734832d3113073022ed2cf2bd2af2aa23c2382302262122091e81dd1d51c41b71a518f18117a17116614613a11f1130fb0eb0cd0c50a208b08507f07506f06e06806005b05905705605305205104f04503e03d03602e02702502302201f01e01d01b01a01901201101000e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x455883036003dd75ce89c738b6c8d8dafb5768ece19832d63cc257f2ec5ceb6559a874f699d3223c4768d915a18410804ff9f33c275ce29c0316618c117b2de598a91472864d49812022841c819001f63b4730d91a23145d8a81482343e0790ea1c0350690c41682a0520a013c2604b0941202183c0760d41682704a08c1101f03c0740d81a0320480881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xcab62a2d35620aad50927893669a149624691fa8db45221dd0b48454079f6cf8477d3b59c84d5a60e2f096d0b4853829494409e84c92539240900457217906c7ce3db19c0c8862a3061740b6455e28913c09804a423a11107c83ca1d50e286703201790b6855826210807d832013609104582040f007603701980be05d02d81680ae05602a814c09204001f00d805c027012808c04401f00f007403601a00c8048022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x70c6e467665160c5bb59d57b5745295225114fd4d94be4b04a949247546844643b4153d037e35d33f3382ed2e62d52bd29a28227426d24f23922c2071fe1b91b21ae1a619618e17b17116b15d15514713c12e12712211d10d1070f90f30ea0e00cd0ca0b309908f08908007707506d06505e05c05a05905605505405204904003e03602e02702502302201f01e01d01b01a01901201101000e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x519a052f653c858ad11e1bc327d2f89ee3cf770e91cc3926fada1ae34367ac9980ace584ad1582794e89b9332564908f51ca2a43685103203352690d019b31c620ba9662c4558a894627649c9211f22e4087d8e91c4354640b716026c460871021e4398720d81902e85b0b21602a8540a61442484007c0d81702704a08c1101f03c0740d81a0320480881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x3dd7a8eddd238a6bad51a2b4263ec758d31560ebf17a2f15ceb51662bd572a9942a5f4a891d2222143e869082013e87b4f59e03ac738de9bb2e25acb21622a45389e93125c4908e91120a3c8770ec1d23706b8cc18e2fc598a413c2243f87d0f21c03586a0c81702a8530a41442704d0981282083b0740d4168260480881081f03c0740d81a0320480881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record011_frame007_links_0000 record011_frame007_links_0064)
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6613145566a9f4a0a43d1fa8d746222550ea8634181fecfb47c93d19e44e3a57f2b590347b63c91d18e406c23411978bf058e2a614a89bc4ba2060ff87e83e61e50ef07043741a60c886082f61750a5851027a13609784a023011108183f01ee0f006a02bc15c09104582040f006e03501a40d0067033017c0ae05602a814c09204001b00c806203001780b804e01f00f007403601a00c80480220100070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa049e993492b84481f80c7e37d27a378f77f7507136ee6dc6b169e67e5d15c84f94dd4cf4af4a147b46c45f4364043e73d93b43a431e3113052f52d92cd29528525a2282081f91e91a01911831731651561351291090fc0f30e80b309f09e08b08507d07606c06806706606506405d05505405305104904003603203103002f02e02701f01e01d01b01a01901201101000e00d00a009008007006005004003002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x5a62c41472a20495a3bd1bc8b8453a2110b88454079f6cf827ac3be1da8e4263130e14d8a0a4f726d1330962492240115c85e41a2050f987b43381910c5460c2e816c8a7051226011d088c4242010d406703201850bc85b42aa14209104582120fb06382ac15409104582040f006e03501a40d0067033017c0ae05602a814c09204001b00c806203001780b804e01f00f007403601a00c80480220100070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6756515cd5c352850a4ff4e84db4c24b24a949247546745c44543a4153913872ec2cc2bf2a729c28627626d24f23922b2202061fd1b91b21ae1a619618e17817115d14713d13913511410d1071000f90f30e90e40d90d30ce0ca0b20a60a508f08908007706d06906806706606505e05605505405204904003603203103002f02e02701f01e01d01b01a01901201101000e00d00a009008007006005004003002000 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1ad8d2f6943461a06cea5ddac51604a4f4d426591e08e946fa34d1988be45ba2b91548a244da2491166c23591a44cbe56d2ae94f0a144c625f92e09664ad253127c93049124412048fa47723791a48b03811b60ad854c27a135893047821a10708003a61c30cb86202d215909b84ac23a0f807803a41c40db06a030815e0ae04d81e00ea06e03501a40cc05f02d81680a604001f80f807a03601a80c806203001780b804e0260118088032012007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb87b36b2cb19af1aaba389d99ca93f8c78b58178077f67d77c379978476976174572e70f6f96266186085e253e52e51c4f14af4a049a49348547a46c45c44d4384264204123f93eb3e336d35a2c42b42932862652552312252151df1d21b51a81871781541451351060f50e80da0cb0bd0b30a80a709907807506e06a06906605f05b05a05304003f03e03d03603503203103002f02e02702602302201901200e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x75b73a73572a71b7046a566965c5fa5be5b655554e54453c53752a52451c5185105095014fa44b43d42e40e39238837535532732031b31831230d3083012fb2f32ec2e82e22da2d42cd26625a1ef1e61d01c71b41a918e18817e15b15213b13511f1170fa0f30ec0cd0c50c00bc0b60b00a609c09b09107607306c06806706405d05905805103e03d03c03b03503403103002f02e02d02702602302201901200e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xac6a0379a78c77c77276375373e72a7166fb6f06de6cb6b069d47446945c4554474394284184073f03e93db3ca3b33a327526725a2492392282091fa1e91a019118317316515613712b11c0f10e60d90cc0be0b20a509f09e09508507607507407306c06806706606506405d05905805104003f03e03d03603203103002f02e02702302201b01a01901200e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb87aab80d7fd7f67ed7d77c37af79978476975b74572e70f6f94af4a049a49348547a46c45c44d43842e4204123f93eb2a12932862752652552342252151c41b51a81981871781571451351020f50e80da0cb0bd0b30a80a709908b07807707607506e06a06906806706605f05b05a05304003f03e03d03603203103002f02e02702302201b01a01901200e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1ad8cea476a3991be8da469a33118a8be45ba2b91528a244da2491164c625f92e09664ad253127c930491244120c8fa47723791a451427a135896c49823c10e88384001a70cb86202f01690ac84e825611d07b83c01d20e206d83501840af057026c11607803b81d80ea06e03501a40d0067033017c0b605a029810007e03e01e80d806403101800bc05c027011808803601a00c804801c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
def record017_frame004_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x75b70455054954454153c53753152a52451c5175105095014fa32732031b31831230d3083012fb2f32ee2e82e22da2d41d81d01c71bd1b41a919118817e14413b13512911f1170fd0f30ec0cc0c50c00bc0b60b00a609c09b09108507607507407306c06806706606506405d05905805103e03d03c03b03503103002f02e02d02702302201b01a01901200e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record017_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record017_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 4)
      (record017.inverseMaps 4) record017_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record017_frame004_links_0000 record017_frame004_links_0064)
theorem record017_frame004_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 4 :=
  of_group record017 4 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record017_frame004_indices record017_frame004_graph record017_frame004_links
def record017_frame005_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1ce6cc1441a1c50be855422a0cd0448103ff1f90fb87cb3dd1e88f2034f19e8cac64231117f8bb85b82ca1580aa052e28613709703681ad0d3067c3301910c185f02ea14b0a204f426c12f094046822610c07a83b81ce0e006c834c1840af057026c11607803b81d80ea06e03501a40d0067033017c0b605a029810007e03e01e80d806403101800bc05c027011808803601a00c804801c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record017_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record017_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5)
      (record017.inverseMaps 5) record017_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record017_frame005_links_0000 record017_frame005_links_0064)
theorem record017_frame005_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 5 :=
  of_group record017 5 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame005_indices record017_frame005_graph record017_frame005_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (Fin.cases (record017_frame004_supported hcells) (Fin.cases (record017_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a60d2e6943479a2ecfd65d326d902c47612af8d656b005702a754faa314a1a4f91be8c945422490488113f81f74f4a78f3b01d44e8473c39c1cace3671037e9bd0dd26d635b1aa8d3c68c34299e4cce63e3149868a904f2274931c97c46222c90e88623f41b30c1c5ea2da16409b84bc24811c084033218f0bb05b028213009204601f00ea070035817e0be05a02cc14c08f04101ac0be054025812806803301600a404e025010007002c013009003c0140070018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1d9cecc7603a45d0ae53703376db68d4268db2d586cc065ee2d91674ad24e826e92d2955499247516c8a243fa1a908483c413205cff87e93ed9f38f867b63d01e58f0e76d3921c64e186f63761b74d8667933919b8b0c54129b9458a184b425512248fe45a1c90cc863a3001760a444f825f12588a43681a10bc85a427213009284601f80f3074036c19a0cc05c02dc14c08f04101ac0be054025812806803301600a404e025010007002c013009003c0140070018008002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x73873672f72a72871b6fd6ed6d76bd6b569064262760f5e95d55a954053a50c5004f04e84b74af49f49347d47746745c44f44944544043742b41b41240e4083f43eb3e73e13dd3d13c13a63a139e33130a3072f52f32c62c42b32b029a2351fd1f11e41da1a619c19018417112f1261101070ef0e60e20dc0c90c00ba0b60ab0aa0a10a009808907c06905d05204904803403302c02902702502001c01601301200f00a007003002001000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x87a1d86a178521083a067f9f67b9e6769d1725c16e5af6759a63d8a60d7e5d16f5a16356d58555545454e5314952146505404f9394e1374d5304bd2d4a1254892043903404fa3e0ed3ace4388d931cb82d0af2aca02709724c8e20c801dc741a46618860164561485012c4a118451083f0ec380c42a09825084200781b064170501203c0c02c080140400c0200400 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
def record018_frame005_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x342e84d039f33de6fc979071be13c11742c0d77adb52a9cd0294527a41c7e8e31ae2444286b0be0cc13808ffdfabee7d6fa1f03da7a8f41e4bc375ae99cfb99728e21beb5969cd3164aa653ca2943a594ae9091e21d3a46a0d018f308578aa9452764907c0f31ce384680cb18e3045b0b215e2a84f89e13025c4807f0ec1902f8540961281a0330580a4138250400700b01302403c0500700600800800 } : Fields).get c.val)
theorem record018_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record018) (record018.maps 5)
      (record018.inverseMaps 5) record018_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame005_links_0000 record018_frame005_links_0064)
theorem record018_frame005_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 5 :=
  of_group record018 5 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record018_frame005_indices record018_frame005_graph record018_frame005_links
def record018_frame006_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x2b1561ac157eaf55aa874de9751ba273ea614b595926249476841069febf27ccf85dbbac73ee69c2b7d6d6d9db0b5d6b4d5da934f69cd2da5347678cdd98b2f65acb192b0e60ec1155a895089d538a4347c8b515a08394690cc18e30e57ca91472824a87b0f01c4378668c71862f4578a91482784a89412023c4407a0e61942d8500921201a0330580a4138250400700b01302403c0500700600800800 } : Fields).get c.val)
theorem record018_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record018) (record018.maps 6)
      (record018.inverseMaps 6) record018_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame006_links_0000 record018_frame006_links_0064)
theorem record018_frame006_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 6 :=
  of_group record018 6 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record018_frame006_indices record018_frame006_graph record018_frame006_links
def record018_frame007_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0799.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0799.count (({ width := 10, code := 0x745d0739cd731ca71dc6709bd6f1b469da56899e671955dd755b16959562551515354a50d3f4d1324c12f4b92c4ad2949d25491234711b4691945d1544d0d42d0a3d8ee3b4e839cdc36cd6354cd2e8b52c8af2b0a52889f27097218821f87a1c4701b86b190631805e1645815c5614c4d11c410e4320bc2e0a0270842007c1e068160440f0380d0280700c0200400 } : Fields).get c.val)
theorem record018_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0799.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0799.localPairCheck (smallEmbedding record018) (record018.maps 7) (record018.inverseMaps 7) record018_frame007_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0799.localPairCheck (smallEmbedding record018) (record018.maps 7) (record018.inverseMaps 7) record018_frame007_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0799.localPairCheck (smallEmbedding record018) (record018.maps 7)
      (record018.inverseMaps 7) record018_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame007_links_0000 record018_frame007_links_0064)
theorem record018_frame007_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 7 :=
  of_group record018 7 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0799
    Papers.RationalityTen.SharedFrameCatalogue.group0799_facts record018_frame007_indices record018_frame007_graph record018_frame007_links
def record018_frame008_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0793.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0793.count (({ width := 9, code := 0x273389bcda6b3499cca632e96caa4d259248a431f86c320f0480bf9ecf3783b5d2e57037dbcdd6e36db4d96c359aad46833d9ccd65b2992c56230d70b3592bd5ca75328d449d48239168a43a1102803e9ecdc6a3398cb85b2c95ca2502713090472311486401e8e8662c150a44c251007c3c1d0c854220f070341407018080200 } : Fields).get c.val)
theorem record018_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0793.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0793.localPairCheck (smallEmbedding record018) (record018.maps 8) (record018.inverseMaps 8) record018_frame008_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0793.localPairCheck (smallEmbedding record018) (record018.maps 8) (record018.inverseMaps 8) record018_frame008_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0793.localPairCheck (smallEmbedding record018) (record018.maps 8)
      (record018.inverseMaps 8) record018_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame008_links_0000 record018_frame008_links_0064)
theorem record018_frame008_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 8 :=
  of_group record018 8 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0793
    Papers.RationalityTen.SharedFrameCatalogue.group0793_facts record018_frame008_indices record018_frame008_graph record018_frame008_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (Fin.cases (record018_frame005_supported hcells) (Fin.cases (record018_frame006_supported hcells) (Fin.cases (record018_frame007_supported hcells) (Fin.cases (record018_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xd3469734a1a32d12687b431a10d0267cb3d19d6ce8671b36998ecc265f32dd962ca664db24990ac8163c31ad85ec0d600afe9788ba95cbadd56c6b355852ba94bea5c4ff27c939c9c24a2a5051b28cb45122510368173f39f8cfa67a63ce9e08ee074739e9c70e086f536e9aa0d28683337997ccb465332598b0c1a6002f51780ba65bd2cf1624af25642aa1540a9254229214109f04e526c933497446b229110c8544272088fc87d83e01de0e506dc3691b10d5c62c30917c0ba45b82cb134097448423711888343fc1f40f3865c31a1740b5059027c12e09204601fe0ed06f035018c07303801b00c806102e814409c04801d00dc06602b0140090012008003800c004001 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record019_frame001_links_0000 (interval_append _ 64 128 161 record019_frame001_links_0064 record019_frame001_links_0128))
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe6372b3925c6ee2c712b865c0cdfd6fb37a9baedd46e6b71db5eda76cfb651b04d7b6b9b5a1aacd526a5b5119eecca655b2658c2c42618305981ebe45d72e15586ab9531a965484a3d4c5260124a91b48223fd10a87e426a12106680d4041fccfd07c03cd9dd0e9e7393971becdbe6c43561a44d0866c331992cc606233059810c005f82ec16ecb4458b2ba15a0aa854d29b147ca264ff27c93d49dc49c23e91b88b245321f90a884841b1fe0f0c7203821b88d8c6603221888c145fe2f714389d84ac24a11f08704202040fd067831e1720b48580282138097849821c0fb07383701a407303801b00c806102e814409c04801d00dc06602b0140090012008003800c004001 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record019_frame002_links_0000 (interval_append _ 64 128 161 record019_frame002_links_0064 record019_frame002_links_0128))
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x4748e11b2344678cb18a2fc5e8b91662b4548a313a26c4c895122224438830fe1dc3986f0ce1542283b06606c08808fedfbbeb7bef59d13a0710e19bf37c69ed3599b3164ec95853075e4bbd732d55a4b25622b355aa854da96520a113c26f4c69692c2534a09111da394688c517a2a446861072033f27dcf91ef3c8768ec1d33a0738e49b434c674c798d3065d4b99702d6568a41462865049792d25449c929222144187d0f61e63a0720e11be31c620ba16e2d0558a814a28c4e09511c228430610be1702b0540a2118220420740dc1982b0500900480800e00c01001 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record019_frame003_links_0000 (interval_append _ 64 128 161 record019_frame003_links_0064 record019_frame003_links_0128))
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1031.count (({ width := 10, code := 0x394e438ce2387e1782dff7edf379ddb74dc76edb76cdab68d9363d875fd6f59d5f53d2f47d0b3ece333cbf28c931ac3f07ba2e7b66d8b46d0ab2aaa5693a2a889ce7098a5f9664d92a44902318ae2086a1583e06805fa7d5ee7b1e7795e0765d7749d0739c9711bd6d1ad691a26759b6518b62584609805ed6b5895b549505213f4f53a4d5274611644d11409003f4fa3e0f5388df360d5350cc324c8318b02b4a32809d250912388c218801f47b1e45f1745a1505213c4510c410e4360c82a09c230240801c0300801 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 128 161 :=
  interval_of_check _ 128 33 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1031.localPairCheck (smallEmbedding record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 161 record019_frame004_links_0000 (interval_append _ 64 128 161 record019_frame004_links_0064 record019_frame004_links_0128))
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1031
    Papers.RationalityTen.SharedFrameCatalogue.group1031_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a68d2e69434319e8ce365bb2498f0bf75c4ad55664b30581ac095c6ae254da9ed4cca6052e28f9422a014f927853a29c24c6259929a9464a0a47d1dc8dd465a2dd14c8944059f5cfa478c3bf9db4ec07513a31d00e7272b38d9c40dfa6f43749b58cb26532ff17a8ba25bd2a795249ec4e526592e884c3e91ee8ecc76038b1c40dbc6ce3621a50d0063030417c0bac5ae2cb136097448c23711888483fc1f40f3866c31a1780b5059028612e09204601d0095049023811408704081580aa05401d00dc06602b014009003e01e00e807002e01400800240100070018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame001_links_0000 (interval_append _ 64 128 138 record020_frame001_links_0064 record020_frame001_links_0128))
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1cc6e56724b865bd4dcd6ca35a1a96c8c611b0317b2bd75d1ae85704b7f596abe95acac755caa694eca6752ca929486a3d4fea71534098e4c0258127692948da43120a8ff43720f10627fc3f89f9cfba7cb3df1ea8f1c77f3b91d78e847383989ca8d0266c310182cbfe5f82b29550a204ff27a13b88a242220d0fc07ce3ba1da0e486f83711ad0d5066431c1888c185fa2f714609d84b424a11f08804202040fd068c31e1760b4858028a13809784981ec095049023811408704081580aa05401d00dc06602b014009003e01e00e807002e01400800240100070018008002000 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame002_links_0000 (interval_append _ 64 128 138 record020_frame002_links_0064 record020_frame002_links_0128))
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x23a4708d918a2cc518910fe1bc16802fd1f4be87baf71ea3d3786ecdd33a3740e65c638970ce09bfb7c6e0d81a9b5069ad119bb34662cad94325602ba572acc590b0d602b9564abd552a7540a754c295524a352ba534708d11722a3ec7c8eb9d339a724c61722de598b29552a8524a21432784ec9812b2544a09192221a4187e8f61e63ac720e11be328620bd16e2d0570a814a28c480730e01b0340670cc128248480740dc1982b0500900f81e03a0700b8140200240400700600800800 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame003_links_0000 (interval_append _ 64 128 138 record020_frame003_links_0064 record020_frame003_links_0128))
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1e34f147863b75d64e8670eb7c9b8cd31683b3c9976cb6638b1b986cc305d42dc1690b38593ac115b4ac655aaa7d516a7d51e28113b89cc4dda6612dc95a4a4a4cd23e911464a2d115e898449a23110686e42f212d06e82540aa008fde7e13e59eccdd26d534199c0c9c6372ca1600a5c51b27c938891247023510f886c3fd1f90f0474c3951bc8dc468c32a18d8c205dc2dc13c89a049623911688343fa1f20f2065830a1680ab052825411a08784041d0095049023811408704081580aa05401d00dc06602b014009003e01e00e807002e01400800240100070018008002000 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame004_links_0000 (interval_append _ 64 128 138 record020_frame004_links_0064 record020_frame004_links_0128))
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73372f72c72070d6fd6e16d26c668565d6476396366236226116105e45d35c85c25bd5ae59258957f57356855e54653652652051b50c4f04e54db4d14c84be48947547245e45945344f44a44543f43743042a42241941340b4023b33ac37536835634a3042fd2c62ba2a729a25523d23722622520d20c1fa1f31ef1e41e21cb1be1b71b01a319c17116c16215a15814913d13a13410c1040fd0f80f60e70db0d60d20c109108e08a08608307d05405305203803603202b02802401f01e01d01c017014010009008007003002001000 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame005_links_0000 (interval_append _ 64 128 138 record020_frame005_links_0064 record020_frame005_links_0128))
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
def record020_frame006_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8de8d98d48b389d88b86885483b7e77c17b47a079f78478376f76c73a71b6fb6f26e76d56c26b96b06a669f69967c65f64c64363a6276075fe5f35e85e15db5ab59559157957556f56c56355955054153952f52651751250b50349048045244143342b3cf3be38837836a36231c3012fb2ea2e52c72c22a228e28426f26a24a23622c22421b2161d11c31b21a91a318f18417e17713b12d11c11110b0f90f00ea0e10cf09509208e08a08708105605505403a03703302b02802401f01e01d01c017014010009008007003002001000 } : Fields).get c.val)
theorem record020_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record020) (record020.maps 6)
      (record020.inverseMaps 6) record020_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame006_links_0000 (interval_append _ 64 128 138 record020_frame006_links_0064 record020_frame006_links_0128))
theorem record020_frame006_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 6 :=
  of_group record020 6 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record020_frame006_indices record020_frame006_graph record020_frame006_links
def record020_frame007_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1024.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1024.count (({ width := 10, code := 0x84a0f83208812007f1f87d1ec79de3775dc755d4739cd71dc16edb96e1b56bdad6b1a969da668d9d65d956519162d896218560d825dd705b966591615795b561555414e52d4850d414f9394a5254711845511404fd3d0f03b4e9354cb320c5310be2f4b82d0b32bcae2a4a5290a12749c2488f22c8821c832007f1f8761cc6f1b06b19c6418c621704b1244711845110390e0370b82c0a42508c200701b06819054120380801c0600c0200400 } : Fields).get c.val)
theorem record020_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1024.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (smallEmbedding record020) (record020.maps 7)
      (record020.inverseMaps 7) record020_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame007_links_0000 (interval_append _ 64 128 138 record020_frame007_links_0064 record020_frame007_links_0128))
theorem record020_frame007_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 7 :=
  of_group record020 7 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1024
    Papers.RationalityTen.SharedFrameCatalogue.group1024_facts record020_frame007_indices record020_frame007_graph record020_frame007_links
def record020_frame008_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1028.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1028.count (({ width := 8, code := 0xdbdad9d8d7d6d5d4d3d1cfcdcccbcac9c8c7c6c4c1c0bfbdbab9b8b5b4b3b1afacabaaa8a5a4a3a09f9e9a9796939291908f8e8d8c8b8a8988878685817f7c7a787672706d6b6967625f5e5d5c5a595756555352504f4e4c4b4a464442403f3d3b3a39363432302f2d2b2a292826242221201f1d1c1b1a1918171615131211100e0c0a07060503020100 } : Fields).get c.val)
theorem record020_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1028.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1028.localPairCheck (smallEmbedding record020) (record020.maps 8) (record020.inverseMaps 8) record020_frame008_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1028.localPairCheck (smallEmbedding record020) (record020.maps 8) (record020.inverseMaps 8) record020_frame008_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1028.localPairCheck (smallEmbedding record020) (record020.maps 8) (record020.inverseMaps 8) record020_frame008_indices (Fin.ofNat record020.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record020_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1028.localPairCheck (smallEmbedding record020) (record020.maps 8)
      (record020.inverseMaps 8) record020_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record020_frame008_links_0000 (interval_append _ 64 128 138 record020_frame008_links_0064 record020_frame008_links_0128))
theorem record020_frame008_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 8 :=
  of_group record020 8 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1028
    Papers.RationalityTen.SharedFrameCatalogue.group1028_facts record020_frame008_indices record020_frame008_graph record020_frame008_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (Fin.cases (record020_frame006_supported hcells) (Fin.cases (record020_frame007_supported hcells) (Fin.cases (record020_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf7479c3bc1c9ee146f33625ab4d0e65d325589ac01578a9d946a9f44eaa6f934e9834b6a53926e91147e233917c7fb3f49edcf4e7863b09c64d9a5bd2a114049804a124511cc89e43920d100c7ba3c81cd0e2858e2b514189cc48021b0f886b032e1910c505ec2ea16e0a184b8250121089043020a0c8056027812a08c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19c4cc264030d5670ac654327312b491a45b22bd13489343e214500c74838c1be4dd26b63499a0ccb86492f9970cb485942b094f8a5c50727a1240912476238117488242b20d10007d83be1d30df06d83431950c044f224b11e08b441a2000f906582d01590a504a823a10f064025411807a03901a40c605a02b81580aa054029014409e0490218108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x20ad0207c2bdc5e48efc77239b5cb4e2f6f4b735b1ed5d695342d974c9561e303d7f0b7f5b6ad1d60eaf155caa394c2a474e425a51ca8c0456a10505e80c3f49ed8f4e7863b09c20db66c432598e4c265d32de9614ab452d289925086a3b11c60de461a2fb16c0ad4504273120086c3d41dd0eb86b034a1970c505d02dc152094048422610507803a416408c03481900c606102e01680ac05502a00c405802b014809004401e00e807002e01600a003c01a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1ed3d87a6f39e0bbd772e89cf395712e0dba3686b2d359b331648c818e305602be1762e65aeb2d5e2b05209fd352654c694126a474848e11b2304568790d2163fe7ecf91e63c0744e29b6354628bc9642be574a51472824f0991302424407d8f61e83846f0d81a6324638bf1722e05b0b41622c0550880ce1883085f0b41602a0530a40c41602b0520901101e03a0700b81602803c0680901001c0280400600800800 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x33c675cd39932d654ca79172163dc638970ce0fbfd7d6f25ddba171ee25acb5568eca588aed5aeacd4ea57406624b69611fe39c6089b0c211c14818ff5f9bf07b0f55e7bbf766e89cb3846f2d4d982f95debb15e2b2548a553fa764a08b0fa1e63c46c8d399a3125d0b514a21c418798e418c2ec4887c0c61782e85b0ac1502804f09c0c41602b0520901101e03a0700b81602803c0680901001c0280400600800800 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
def record024_frame004_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x276ce49ab346614b996f29250c9c92722e40c7a8df19e29c4f8850e21b42284106e07c087fcfddf6be5786ea9c23786e2d49a5b3e662c6d8a30a604bd1762ea5a4b4566abf56eaad502945169ad2b22c444874fd9f43d6788e69c735a63cb69622bc4f09c12a23e430840f21a432c5f8b514a280450770ca1802f85d0b41602a0530a40c41602b0520901101e03a0700b81602803c0680901001c0280400600800800 } : Fields).get c.val)
theorem record024_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record024) (record024.maps 4)
      (record024.inverseMaps 4) record024_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame004_links_0000 record024_frame004_links_0064)
theorem record024_frame004_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 4 :=
  of_group record024 4 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record024_frame004_indices record024_frame004_graph record024_frame004_links
def record024_frame005_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0844.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0844.count (({ width := 8, code := 0xf5f4f3f1f0efeeedecebeae8e7e6e4e3dedcdbdad9d8d7d6d5d3d2d1cfcec6c2bebdbcb6b5b3b1adaca9a7a6a5a4a3a2a1a09e9d9c9a99918d89888781807e7c7877716d69686761605e5c5857524d4c4a494645433f3b37363533312d2c2b272322211f1d1918171312110f0d090807050403020100 } : Fields).get c.val)
theorem record024_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0844.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0844.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0844.localPairCheck (smallEmbedding record024) (record024.maps 5) (record024.inverseMaps 5) record024_frame005_indices (Fin.ofNat record024.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record024_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0844.localPairCheck (smallEmbedding record024) (record024.maps 5)
      (record024.inverseMaps 5) record024_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record024_frame005_links_0000 record024_frame005_links_0064)
theorem record024_frame005_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 5 :=
  of_group record024 5 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0844
    Papers.RationalityTen.SharedFrameCatalogue.group0844_facts record024_frame005_indices record024_frame005_graph record024_frame005_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (Fin.cases (record024_frame004_supported hcells) (Fin.cases (record024_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x4151ffaf7478bbb75cd8e2e6f33741ab4d2a68732e992ac3c607afe15daa6151ba7d13aa9be4d3a60d2da92c488a39519c8ad41fa0bd0147e93db1e9cf0c7613841b6cd885b9296940c9804a124511cc89e4391fc0f7476239a1bc8c2c5f62d615a8a084e624010d87a83ba1d70d286282f81740b7050c25c12809084141de0e9056028c13c08c03981c00d206302e01680ac05502a00ec070031015809004401e00e807002e01600a003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x55eaa14fa9ad0d9d736e6acc49712ce3ec57893071f9be3786ef1d83a4724e2dc0b776c4d61a9b35650c7189b065eab8d6cad657eab95229b5069ed35a644bc8f51b22b44083d04a003ec7bcf61e53c2760e59be36a6b4cc190316618ab14326a4b8928fe1cc3806c0c31642b03e06d0d41903005a0b0150298520a013c268460820e81b8300560901101e03a0700b81602803c0680b0120200380400600800800 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x83e4071f84f8c79bbc99de6e5c70a3625abed2c68732e992ac4b61db03d79abb4578a979420a024faa78d3969b04d3a52d26e91447da3a119c8c0421a0b10187fb3db9e90f0c76138b9c1cdb669934016f4a544dc267130495e49723e11cc82e4031f00f1c76839a1c60c3c5f02d81638a0c4e024010d87c83d61dd0e806b032e1910c505d42a414209d84a022610c08203c01c20aa04f02300e406a03481840b405702a815007403201880a404401f00e807002e01600a003801a00a004802000e0050020008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x82b3ff1ee8efb770b939bc4d886953441974c9560fadfd6dab47583abc54eca6151aa7d13aa9be4d3a60d2da8fc472a2f915a87b42620bd0327e93db1e9cf0c761375992cc726132e996f4a8452d280930094248a239913c8723c81d88e286f234718c0bec5ca2b514109cc48021b10087c43d41d70d6069432e18a0bd85d02dc14309704a024211208283a415809704a02300f406903181700b405602a8150084031015809004401e00e807002e01600a004001e00d004802000e0040018008002000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017
