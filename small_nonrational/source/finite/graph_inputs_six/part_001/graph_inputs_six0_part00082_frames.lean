module
prelude
public import GraphInputsSix0Part00082Data
public import RawFrameSupport
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe22e15dfadbbdbada9d97d86d77d14d07ceccadcacc9bc89c78c69c15bd0bc5b04a71a64a129e69249178d58b28468288157e37d27737646ee6dc6bb69e67b5b95ab56f5625524fb4d54c74af4a14834514434363f53e73d93b43a439632d3012f12d92cd2bd2762682081f91e91d81c21ba1ae19c18d17316513512910d0fc0f30e80cb0b308c06d06705e05505304604503703203102d02c02801f01e01d01301101000d00a008007006005004002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (embedding record001) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa66d2d68554169ca4dfe6df357975cb5257f29e93249462e315a8a244c21950b685142260a103975c37e1ad2d2d68d344da06cfc67b2b59592a9d53ba5a92ba931485a3a11b08d4466231516a8b0453a28d1368944459a58cfe64c31c1504a544f727192e89684ab253126091e48a24211ec8ee4712348d1865c2d914289dc4d622d10c082c4001f20d1065031014a09a84a023a10f07c83c41d20e206d83500e806f03681a40ca06002f016807603701a00c4058028012808802600d0050024010007002000c004001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x29a74c2a3fd1927fb3e29cece266cd35291fc8aa3f31e08c2c5be25911987bc389c74cba652b13d7aaa5552027a93889854b925ad2b69544a724ad24891c481a4011f48f3475a3911b286b3611ab8caa61b2ba14eca5250527a138090e476233908c8224011f88f847583051660ae852c285138886040e1f80da06883241820b9055c2a01490a004e426812d093047423010f08484141fc0f507803a81c40dc06b034012408c03781a406e03101680b0050026012808803e01e00e8070030017009804402000d0050024010007 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x29f74efa11503a6df357975cb525852ac950ca2e30b16e84d42060b70447e1be99ebcf4f6b4b451a24d0367b33b976aad15642a754eea494b2a57126290b477a3a11c28dc46aa31517c8b5453a2891368954459a30d0063831414dca564e326992e89684ab253126091e48a24211f48ee46f2348d2065a2d914c8a3c4ec24c10c08384001ef0db06b032616909a84ac23a10c07c83c01d20e306d835016a0a103781b40d206002f016807603701900c4058028011808802600d00580280100070028010004001 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x13a39c74aa651126e92dc6162dd09a840c16e088fc37d33d79e9ed6968cb4499eccee5daab71590a77524a5c12b890b477a3a11c28dc46aa31517c8b5454a2891368954459d6cd2068031c18a0c0c53b295938c9a64c826092e89624ab253127c93048f245120c8fa47723791a488e3421968b645722a914c8a184ec25b126087441c2000f7875838c1b60d1864c2f016909d04ac23a10c07b83c01d20e306d83500de069030016807803b01b80c806202d01600a0046022009803401800b005002000e0060028010004001 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2edd61fb0257e2b7f45a9954c4660b2c78e8c6e2359130892433216f092676ade9514a75511a7b52168f94562269116879433a0890207f63ee1f2cf747903231558a824ef25c8f5c78a3781b30d5c68a3331770b705842a814b8a184b824e0fc87c83ac1d00e487083761b20d5867c3301830be05d42da1600ac854827a136097848423411308603d41dc0e706c834c0de06903281900c005b02d00dc06202d01600a004602200c005c02600e006803001600a004001c00c005002000c004001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe1fda6da0d93d7fd11c98c92c85c71c0dc05c01bc3bb9b88b7bb63a2a99291e9118d58b081b8087be7a879c79378373e72a70e6f06de6cb69d62f5bd5af56f5524d94cb48f4804764704634284183ff3e93db3ca3a33953042f42bd2ac2a02962862732652492392091fa1e91da1c21ba1ae18317316514613712b11c0f10e60d90be0b206d06706306205e05905803703102d02c02802302201801701300e00d00c00b00a008007006005004003002001 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa56d09281b3c69c94d6e2db14288abe39eecf607a73cd9e40d80673b2c591ec815ceabed59caab55225ed2cc91b484a32116686842b213508a83d4179ef4eb27453899abcd3667c33a99bcca664c32296c0ad854f2a29498a144fb26f930897049923e91b88ca46122d914472834f1a08cb85fc2ee16e0ab854028d12e8934476232115088c42a1c90db06882d414509d84942100fe07403480be05c02d015c0aa02d0138098048022010807c03a017009004001e00d00580280100040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5e72edd75ba4e516a88d1d48ddc6ba3311808b9b39188cbc95d9ade9606af05642ad1540a5051da89d21c8fc456a2650a88443fd9fa0fb67ca3da9e4ce2469533f9918b9e5bc2ca1600ad851c28393cc7b43c81bc8d946403101638ad054e296140897c49c22310e083c4102010fc07c43ca1de0eb873c3921c20dd86c835619f0cc06443121810bd05cc2ca14a0a184f425011908904141ec0ef07103540be05c02d015c0aa027012008803e01d00c005c024011008003c01a00c00580280100040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x4eda70535a8b6c50a22af8e7bb3d81e9cf367903205818baf5ceada961aafb56dab5559cab2555aa912f096648da42518a8b3434215909884541ea0bcf7a7593a29c4cd5e69b33e19d4cde6533261914aa654528513ec98c4b823e91b88cc46122d914485a3a81ca0db46be34f19e8cb861c2fe1770b705982be1570a7051a26d12e8934476231115088c42a1cb0db06882d414709d84942140fe07403480be05c02d015c0aa027012008803e01d00c005c024011008003c01a00c00580280100040018008002000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x1e93d079aed9d9fb0f2ae4fc9791f21e3da072ae26c3b832eddd2b8b702dd5a3b39656855019b534254c9f8ed1ae3145b8a912a133f57d8f6dd63a372ce45c5b746dad996d2d054ea713aa6c48a8ed19a2c44a86d079ec3ce770ea9ce3886f8d81a9344668c918b3085e8ba1662be560a814a28c5089d12423a460838f91e238c690ca1782b82e85a0b0154298270480880f81d03005c0901102003c0680c0160280400400600800800 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe33e1fe0bd25d11cfdc0ec06c02bfabf1be6a229e59b89ac99295f95493e93592c8f58e88d981e80b7bf7a77717627136ff6ef6dd6c66a067c65464962f5fd5f15d95d25c95905835734dc4ce49047f4544464043f43e83da3c53a639535134432d3203133032f32d92cd2be2ab2a02962862732652492392282192071f81e71cb19f19018315613612a10b0f20e70ce0b405d05a05805505302702402201f01d01801701201101000f00d00c00b00a008004003002001000 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x92d92591c86e86685d7ab7a57a179a79478f6466185f95f15de5ba5b05a159c59156f56155a4e04d44aa49d47a46e43c42f42841b40e3f93df3c13bb3a538137b36836135c33332b3212a429e27126423f2372031f61ec1e31d51c01b919b19518b18718117a17516c16616115c15715414f14714113813212d12812311d11610e0ff0fa0f60e50d90d30c90bf0b90b10a905805505305004e02702402201f01d01801701201101000f00d00c00b00a008004003002001000 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x1e0fbff7de61ca7926d6da5b3b65ec7d878f311e08bfd7b2ea5ccb716d2d8da0b3b6669451c9db37a5ecb59031ca354668c114a1c41b823001f23dd794f19e1bb275eeada0336618c01722dd560a914ea9a52aa2d40a4e4848c114220432840fe9f23d8778ec1d2396704dd1a533c650c317e2f45d8b49462764c4860f31d2368628c115c26c2a8520a0134258270480880f81d03005c0901102003c0680c0160280400400600800800 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame006_links_0000 record009_frame006_links_0064)
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x14668bd169cb38e70caf95b2ae54ca794b0b60d4087fcfc1ee3d478cf0ddf3b1756ea5b2b5c684ce59231d5fabd177aea5c8b7567ab9564a9148a8e4fa9e53c2674c89810ba113e27a0ea1d23686acd29a1336650c69702d4588ae9592a6538a293e2724cc9812d24e4848e11321a41c808fc1ee3d4788de1b4360620ba16a2b8528a11322482985009c12c248270480880f81d03005c0901102003c0680c0160280400400600800800 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame007_links_0000 record009_frame007_links_0064)
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18fdc156042f395edaead6d6adb49ca29513a7593939bdc9ea4b123f916c6ba33d1868b4c4da1890af847339188cbc95d9ac05568a50513a5b123c8c1456a10cff67e63ed9ed4f2671234a99fcb9a58028e13cc8703ea1c68de461e2c71590a9c50225f127088c43820f10408043f01f10f287783ae1cf0e106b034c19f0c886042e61650a9050825e12809004641ec0f007083540e806e02e81700b405702a80f006c025012008803e01d00c005c024011008003c01a00c00500240100050020008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe22e15d5bd14d07c4dc16bfcbe8be0bd1b86b67b5da258d68b287086184683a82d7e37d27c27737647136fa6ee6dc6c469e67c6546495be5b057056155251e5114fb4f24e74af4a14934514434364043e73d93c33a439635334632d3203132d92cd2be2762682282172081f91c21ba1ae19c18d17316515614313512911a0fc0f30e80cb0b308b06906705505303603303102d02c02701f01e01d01101000f00d00a008007006005004002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x158aab0494a47b1a08cac5fe29d09c847c1fa0550177ffbfb1d8cdd76c834a9a2ecde661b1f58a6c465b92cad58aab253ca9794309ee4f0a5f52b494c49f24dd260914486a4191ec8e846d1c84d9469932c98f0b34545296138499c49a24811cc886432210105c7de3e31e78cac5ac2bd139097c45622110207503861b10d406002e81600a4049423c10e08503b41a205e02e01680b205802b815408003b01b009004402000f807401e00d00580280100050020008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xa90540e83d4139fc4efa621304976c94a47b1a08cac5fe29d09c847c1fa0550177ffbfb1baed17629b1196e4ab24f727852fa95a4a624c121a9064742368fea72134c9964c7861e2d69668ac253929614149c24ce24d12248e644321910807de3e31e78ebc67c32b1790b2857a296139097c45621a10207503861b10c005d02c01560a7852025812508f04281de0d102f01700b405802b815408c04001d80d804c024011008003e01d008803c01a00b005002000c0050020008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x508a81d1858b7428210f02980bbf19f52f867ba3971b38d696a1b4f1a4cd1a681b3d59debb55a52ce95faa9d53c29253bc9ce4c8a4c52188ef47423851b88d5462a2f916e8b1453a28913288b3731a58c726272c895049c84d225d12d09564a624c124491048423e91d48e24691d48b6853228f13b093047822a10c083836c1ac0c985a42b214709a84ac1f20f0074838c1b60d403681ac0d205e02e016807603601980c4058027012008801e00d00580280100070028010004001 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x164fb1bd86ac0f575ab0d476a0136c9ac4cea64724f91d44ae2310c7857409a026ffa7f3b751a28c505b7aabd3d69c44cda6512fc9724ada53528e931492a43920e90147d23c91ce8d93fb9c8ccac61b2d59660ac253b28293849a049a23a910c864422208900875833c1948bc859829613909844562060ea070c3661a20c9855c2a01490a004e426812d093047c22c10f085840c1fc0f507803a01c40de06b034011c08c03581a406603101680b004e026012008804001f00e8070030017009004401e00d0058028010007 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x7a7f4be8bd0791f1fe1fc1f49e91d079f72de53beb7cee8dcbb4b676c7d87a2b3163bc11732cc589ac555a9f52da173d6734cd97526244c7a8d719e2ec4f836f75d539b6dcd89a6b3c63cc31802ec5b2af1582a4538a6540a4e4848a10c9fd3d8778e59ba33c650c317f2f6590af1542864e09992823a43c7c0f01d63806d8cc18e2f85a0af1402683d0780c217c1983105a0b0138260480881001f03a0700c0170240440780d01602804007 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x5e7bc9782ee5c2b816dad9582b015e6bb564ac34de9a527a4944a8850ca133665b4868cf116094057e0fa5ec3ce774ea9d139070cdc1b335e6aad3da3b3f638bb15daae518a0d3b26b4ba93921a3144a841039fa3e87bcea9b6356668c797a2d6578a81452664ac9011922a4007d8f61da39c728df1b0348650c618a2f45d0b015c2a0518a012c2443b8750c41801882f0580ac130250460840f81e03806c0c0170240440780d01602804007 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x7ecbf2df78fae6b4b50da78d1968934299eacea5daad29674adc56429e14c0a494ef27392e095c48623d11de8e8470a3711aa8c545f22dd1628a9451226512a88b3b09becdd669534298e4c4460c2d31658a8053027213349904c125d12d495e49f24c124491648323e91d48e446916d0ae455229912d893047821d107075838c1b60bc05a42b213a09583dc1e00e906d835015e09b03581a40b805a01980c4048022007803401800b005002000e0060028010004001 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x90147ba3bd1c573737c1baed646a634c59d4cc15beac195e6a8d53c28914149f34c125bd2208fe456a251116879433a1710968224081ff8fe27dc3e59ec8f5c7903249748b7e5592a213c09ac4bf22710ec7b83ca1bc8d806ae3451998ca062e2ee16e0b2857a2a814b89f84f425c0eb87243841bb0cf86603221830be05802b215209b04bc25011a08983d41dc0e706c834c15e09b03581a40b805a01980c4048022007803401800b005002000e0060028010004001 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x9049019008ff87485484e83082b82381080578273c7326fb6f16bc6a969564963d6015f55b659f59858f58758257a56755f55654f54553d53352f52449b44f4434073fb3bc3a539434e34430d3032ce2bb2b52ac2a429f29728427c27326c26225a25024c2411c31b71b01a818818117916916214513e13611610f1070f70f00d40d00cc0c40c00a909b06b06905c05a03303102402200f00d00c00b00a008007006005004002001 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xc1cc17c11c09ac5aadaa4a73a66a55a28a039939629579219148d68be8b287086182080d7bf7a279c79378377976a73e72a7167076f06de6c36bd69d6306005f45c05b257055c5545235164de4d049047a47647046345944b4284184073fb3e93db3c23be3a32be2a02962862492392282091fa1c21ba1ae17316515613712b0f10e60d90be0b209f09506906705a05803303102402200f00d00c00b00a008007006005004002001 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record019_frame004_links_0000 record019_frame004_links_0064)
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x50a28293e89e8cb9e5a11e08e9453a27510b879c32a16d02b80cbff9fe0fde7e0bcfde6ce657263695b18d4969db4c1a22d0b67f33c1964b4f58dab5555e9e34d7a5a52868ca45ca2c914689b4492124fb67a73839bf8da069833b1984c9462d2d916a4af654329094309ea4d825d12a092c48f24591ec8ee47223590d07da3c81cf8ce863a28d132897047023210e082c4001ed0d506082f21550a784e425011d08503c41d20e406e03501720a503f01c80d406302d80e006e03401480a004a011005001c008001 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x283d40a9f64f565ef2e08ab43721af0c38114042012ffd7f7bbe5c88d846a433c9964c615ae2cb55589f04e0a5011c08ba459a284f3278336f19e4cc263e3151624a4850c274935491c47c23a11a880c3b71d58e7062626e12e092048422e10e08383f61f10c585e42ca15f0a584e4256118087039c1b409304902380fc07c03581700b005702a013008c038014808003a01c00c004401c00b0038014002000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (embedding record032) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x132296cc8ba3d919d868430a1790a583d40ce030ffa7e53eb1e92f067793845bc4dcc6a23265860c0f5c22b49572a7252ca925486a3d4d0260127691b48624111fe87e42420cd0107f33f41ca8d2866c319982cc0a5ff2fc1604aa852c27f93cc9dc47d22c914c85442420d8e486e23321888c185fa2f714e89d84c825a12508f845422010808103f41a40c785a42c013809784981f60e706e03480e807103681840ba03a01b80cc05602901400940480140080024010007002800c004001 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1894c3ee1430737bbbd3dba2d9765ba71d25a8133e99e64db26c730c95dca8a5072638f1c72a36b19d8c2c5da2a913d898c41a1db0e285c428e132ff87afb551a1ecfe548a94946c9834aba4191cc8d9461a15d03280a3fd1f4cf8a7a63ca9574a3c502227908c7a43b21d28e3c6462e516b0b1853e29113909844562140f987ac3b81900b6859c25c12108904301fc0ef074838814209404801c00d8063030016c0aa05401c00d0056028011807403801600a004c02000e005802000e0040018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa6f52e6929468a11502e76537e99f4c0a57d2aa90745a227b100865c2220f1044804be65eb2edc76ab8d5c48c98644b1fd78cb245672b0156eaad55329814429774a7a5112669154622271122880431211507a8374189d68e6c6b03461984cb664a32318fcaa453c2929454a084c5257926091047723091748ae4511f80cf866031a1878be85e829d14789e44dc25912988a844a21c10b072834e18a0be85c029013b096049022a10b07f03bc1ce0d8069027012407c03901700ae04201c00a804401d00c004001c00b0048018002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x9a74c5a60b2cd94449764091c88dac5e62bb13688c43c6042ff07ef3f4df44f907a8bd11e1cf016a8b501836c135b72ad54aaa4a52228d53f499a4be24d522e90b48323dd0c084c420a0810188013f39c94e3a66f30717f8be65792ab9490a044fa27993a897045d217106871236e1948c3860c2fe17809dc4b024d11e88784262030fd06ec32017e0ba05b02be14d0a184ec25c126083824c11e08403f01880bc05702a8150070034014809404001f00e807002c01200700280100070020008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1894c3ee1430737bbbd3db8ed8d69cb43d96e92d4589f24f1e76339a9c0cdb26192bb9514a0e4c719c8c245d61710a384cbfe1caad54694b43d9fca91530294946c98348323991b28c342ba0b903280a3fd9f4cf8a7b73d31e54aba52c28f140889e3d21d90e9471e32317d0b945ac2c714f8a4450627213087cc3d61dc0dd86903221750b6859c25c12809084482180fe077838814209404801c00d806302d815c0aa05401c00d005602300f807403801600a004001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x163bb11d69eb2957cab454369e143ea11cffe7c93b9946c9da4bd1d68dec6923371858b7c50a26b122806bff5fd4f767b6bd91980c8e63f31a14b6a2950ca80d2d09604a8a46521890647823a91c48dc4191e6cd7869733f99b8b5c53a295945ca0e4f224511948a4442219103c8023f11f00f4467e2cb15e0aa053028310d87d83c61d30e186803241820b8858829013a08f045c2080f607483740c606102e816c0ae05502a011807203501580a404a02300f807403801600a004001c00a004001c00a0040018008002000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994bf35ee6f4b76db5bdab6cf166eae05682b0b560a4b51627c93c79d8ce6a70336c9864aee545283931c67230917585c428e132d2967f30294c0a4f51b26012128e646b230d05c80a3fd9f14f6e7a63ca9b58a5851b28111307aa3b21d10e3c5f42d61638a44506272130891c47222210787cc3d61e30ee06ec34819e0c886082ea16d0b3852826a12e094048423211208603f81de0e203f01c00d806302d815c0aa05402300e006802b011807c03a01c00c005802a014008804001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332992fc7b628b119875c126042fcd6e1b625ab6c01549a98547a96b4a1a4b4f8a78b3ba9cc4dfe6e933b9914c323391848bac2e2147099694b3ed6d0a8a53028e93008fa47322fd0a882e40e2030ff67c73db9e98f2a6342ab14b0a0c44c1e30ec871632017d0ba05b02c71498a0c4e426112388e44441f90f987ac3b81c20d9069032e1910c185ec2ea16d0b3854829414409a84a024210c07f03d81e00e2038818c0c205d02d815c0aa05401c80ac052025011807c03a01c00c005802a014008003801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record050_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record050_frame001_links_0000 (interval_append _ 64 128 130 record050_frame001_links_0064 record050_frame001_links_0128))
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (embedding record050) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994c97e3fb19d8b8c515f9adbf6c2b5bd802a8f52ea92525a8993e29e2ceea73137f9ba4c325872a8944c9963411888b5c2ea14b09369633ed608a5e51d277536c90d47422fd0a682c40f2030ff67c73db9e90f2a5d029514189524821ec8ed071631f17c0ba85b02c71498a0c4e026112388e44441f90f987ac3b81b30cf065c32218a0bd85d42ce1600ac854829213b094046821810407f03dc1e00e103901a80c406102e815c0aa05401d00c8054029012807c03a01c00c005802a0140080038014009004001c00c0050020008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record051_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record051_frame001_links_0000 (interval_append _ 64 128 129 record051_frame001_links_0064 record051_frame001_links_0128))
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (embedding record051) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x167eb3cd9baca3639b10d79abbb5c9aa8552ea7d4e7a70d3428af43ca10ceba74d3929bf4dc66bb34899acc7a6192f596f4a364ed25e8eb46f634919b8c2c5be2851358914035ffafea7bb3db5ec8c8e63428a54069bc4d7265d2dc9684b0254523291348624191e08ea4712370d2e66e304178cb5453c295945c9e446522a11088644011f88f807a23991ba0cec59a2bc1540a0c3ec1e50e9870c3241820b885882ac14f0a404e823c11708804101ec0ef07483740ca06303101840ba05b02b81540a802d01580a8052025011807c03a01c00c005802a0140080038014008003801800a0040018008002000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame001_links_0000 (interval_append _ 64 128 145 record052_frame001_links_0064 record052_frame001_links_0128))
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
def record052_frame002_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19a8ccf66532ab93bc97e33b1718a2bff5fcafcd78fbbf5db6dbf6c2b5bd8d2c33600af5d74eb8159eac1d5d2a8f52ea9252d69434969f14f167753989bfcdd2677322986467230917585c428e132d2967da9814749da4db25f12168fa47322fd05c81e4061fecf8e7b73d31e54a5850625312088903d71e30ec87162fa1750b6058e29314189c84c224711c88883f21f30f5877034819e0cb86442f61750b6859c2c01590a9051025012108d04301fc0f707803880ca06303101840ba05b02b81540a802d01580a8052025011807c03a01c00c005802a0140080038014008003801800a0040018008002000 } : Fields).get c.val)
theorem record052_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 2)
      (record052.inverseMaps 2) record052_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame002_links_0000 (interval_append _ 64 128 145 record052_frame002_links_0064 record052_frame002_links_0128))
theorem record052_frame002_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 2 :=
  of_group record052 2 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record052_frame002_indices record052_frame002_graph record052_frame002_links
def record052_frame003_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x4db9b1356684cb98d2fe5dcb79552a2534a193d26e43c849031d23846c8cf18a2ec578a513623c4387f0f61dc3985b0aa13c258470861041c830fc1f6bea7c0f79ee358696aed5729351aa0938a6f4d69912624a48e9151da3946a8ccda9a831a61cbe16b2d2594af1462885049f9352664bc9692423c44c811001f83d46e8db1b0358660ca18c310608c017e2f45c8b816e2d4598b21622bc318610c017c2d8590aa14c2902d0560a81482504607c0e81c0300580a8140200380500800e0180280400600800800 } : Fields).get c.val)
theorem record052_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record052) (record052.maps 3) (record052.inverseMaps 3) record052_frame003_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record052) (record052.maps 3) (record052.inverseMaps 3) record052_frame003_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record052) (record052.maps 3) (record052.inverseMaps 3) record052_frame003_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record052) (record052.maps 3)
      (record052.inverseMaps 3) record052_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame003_links_0000 (interval_append _ 64 128 145 record052_frame003_links_0064 record052_frame003_links_0128))
theorem record052_frame003_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 3 :=
  of_group record052 3 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record052_frame003_indices record052_frame003_graph record052_frame003_links
def record052_frame004_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x2b9ae2b7adab5ad2b3acab1ac2afabaadab2abaaaa9aa2a7a9aa5a92a3a8aa1a829fa7a9da729ba6a99a6297a5a95a5293a4a91a428fa3a8da328ba2a5f9621c855fe7e1ee779dc761d16e9b86d5b36a5a768da15d16d55950519364d1304a5124410d42d013fcfb3e4f13ace1344cf32cc42b4ab2a0a62709a258942449023c8d2248821c8520c822047f15052144501304a1184410c2d0ac2a0a42508c1f0741c06016054140400e0280801c060140400c0200400 } : Fields).get c.val)
theorem record052_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (embedding (N := 44310) record052) (record052.maps 4) (record052.inverseMaps 4) record052_frame004_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (embedding (N := 44310) record052) (record052.maps 4) (record052.inverseMaps 4) record052_frame004_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (embedding (N := 44310) record052) (record052.maps 4) (record052.inverseMaps 4) record052_frame004_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (embedding (N := 44310) record052) (record052.maps 4)
      (record052.inverseMaps 4) record052_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame004_links_0000 (interval_append _ 64 128 145 record052_frame004_links_0064 record052_frame004_links_0128))
theorem record052_frame004_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 4 :=
  of_group record052 4 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record052_frame004_indices record052_frame004_graph record052_frame004_links
def record052_frame005_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x629c4d8930fe1ac3184f08e0dbf77e2fbdf0bdd7aaefddabb1732e55c8b8f716e1dc1b7d6f2dadb2b6168acf59ab075febdd78aed5d2b7d6dad753ea6d4ba6d4d2994d199112e2142082900deb3cf78aeddbe3766dcda1a9b4b688cf962abd544a654526a4cc97d2aa294488790da0f41681d021ee3c0724cf99b32661caa9502925189a12d25049490118224408710dc1ac3205f0b8160290318610c017c2d8590aa14c2902d0560a81482504607c0e81c0300580a8140200380500800e0180280400600800800 } : Fields).get c.val)
theorem record052_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record052) (record052.maps 5) (record052.inverseMaps 5) record052_frame005_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record052) (record052.maps 5) (record052.inverseMaps 5) record052_frame005_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record052) (record052.maps 5) (record052.inverseMaps 5) record052_frame005_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record052) (record052.maps 5)
      (record052.inverseMaps 5) record052_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame005_links_0000 (interval_append _ 64 128 145 record052_frame005_links_0064 record052_frame005_links_0128))
theorem record052_frame005_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 5 :=
  of_group record052 5 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record052_frame005_indices record052_frame005_graph record052_frame005_links
def record052_frame006_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x75eeb9d6fa874ae8bcdb9872ce1dc3786700dffbdb6eed8da5aff5eebbd73ae35beb4d5faaf50e9dd31a1740e7ecc597b2d657ca994724e45c87816ffdfabab74ae7d1ca1b1de34c468750a1ff3f57d2f61ccb92710e05b53636b2d4555a9f5069ed35a4d4949151da0d40c800fc9e53c076ceb1c23726b0c197d2ea59ca013c26e4d492121234458879092083e8710dc1ae330620bd16e2b8318610c017c2d8590aa14c2902d0560a81482504607c0e81c0300580a8140200380500800e0180280400600800800 } : Fields).get c.val)
theorem record052_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record052) (record052.maps 6) (record052.inverseMaps 6) record052_frame006_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record052) (record052.maps 6) (record052.inverseMaps 6) record052_frame006_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record052) (record052.maps 6) (record052.inverseMaps 6) record052_frame006_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record052) (record052.maps 6)
      (record052.inverseMaps 6) record052_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame006_links_0000 (interval_append _ 64 128 145 record052_frame006_links_0064 record052_frame006_links_0128))
theorem record052_frame006_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 6 :=
  of_group record052 6 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record052_frame006_indices record052_frame006_graph record052_frame006_links
def record052_frame007_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x4849072063ec798f11d63a4728cd1963245e8bb16e2a45089f122234448871061fc3c8750e61ac328630a613c268350620bc1582904e0840e814ff1fd3f67dafadf53c177cd59a833b66ccb98bb1561ec19732e05b6b51632c057cae92b25147a8e118215420825001df3b8764eb1c73866f8de1af340630b19622ae5349191c22c4447f8f81e63bc768ea1cc370638c31802cc548a513c24c2d8590b015c2985209c1302582c0540a41402404407c0e81c0300580a8140200380500800e0180280400600800800 } : Fields).get c.val)
theorem record052_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record052) (record052.maps 7) (record052.inverseMaps 7) record052_frame007_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record052) (record052.maps 7) (record052.inverseMaps 7) record052_frame007_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record052) (record052.maps 7) (record052.inverseMaps 7) record052_frame007_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record052) (record052.maps 7)
      (record052.inverseMaps 7) record052_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame007_links_0000 (interval_append _ 64 128 145 record052_frame007_links_0064 record052_frame007_links_0128))
theorem record052_frame007_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 7 :=
  of_group record052 7 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record052_frame007_indices record052_frame007_graph record052_frame007_links
def record052_frame008_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0811.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0811.count (({ width := 9, code := 0x12e96cb2572a94ca24f2692c92472290c823f1e8ec72371a8cc622f168ac52271288c421f0e86c32170a84c220f0682c12070280c01fef87b3b1d4e370b75b0d76b34990c662b1182c05faf56ab3562a94ca15027d369147a391a8a44a210c813f9ecec753a1c0cc6431988be5e2e96cb2582b954a250279389a4c259287a3b1d0e46c35190c05e271289046200f87034190a84c2411070341408038180a04018080200 } : Fields).get c.val)
theorem record052_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0811.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0811.localPairCheck (embedding (N := 44310) record052) (record052.maps 8) (record052.inverseMaps 8) record052_frame008_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0811.localPairCheck (embedding (N := 44310) record052) (record052.maps 8) (record052.inverseMaps 8) record052_frame008_indices (Fin.ofNat record052.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record052_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0811.localPairCheck (embedding (N := 44310) record052) (record052.maps 8) (record052.inverseMaps 8) record052_frame008_indices (Fin.ofNat record052.n i)) 128 145 :=
  interval_of_check _ 128 17 (by decide +kernel)
theorem record052_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0811.localPairCheck (embedding (N := 44310) record052) (record052.maps 8)
      (record052.inverseMaps 8) record052_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 145 record052_frame008_links_0000 (interval_append _ 64 128 145 record052_frame008_links_0064 record052_frame008_links_0128))
theorem record052_frame008_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 8 :=
  of_group record052 8 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group0811
    Papers.RationalityTen.SharedFrameCatalogue.group0811_facts record052_frame008_indices record052_frame008_graph record052_frame008_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (Fin.cases (record052_frame002_supported hcells) (Fin.cases (record052_frame003_supported hcells) (Fin.cases (record052_frame004_supported hcells) (Fin.cases (record052_frame005_supported hcells) (Fin.cases (record052_frame006_supported hcells) (Fin.cases (record052_frame007_supported hcells) (Fin.cases (record052_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record052_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082
