module
prelude
public import GraphInputsRow28Part00000Data
public import RawFrameSupport
public import SharedFrameGroups002Checked
public import SharedFrameGroups003Checked
public import SharedFrameGroups004Checked
public import SharedFrameGroups005Checked
public import SharedFrameGroups007Checked
public import SharedFrameGroups009Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups042Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups057Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups079Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0017.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0017.count (({ width := 7, code := 0x3af4e7cb8f0cf9b2e4b76abd6972a4c87ef9dba5eb95aa3e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0017.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0017.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 58 :=
  interval_of_check _ 0 58 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0017.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ record000_frame001_links_0000
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0017
    Papers.RationalityTen.SharedFrameCatalogue.group0017_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0403.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0403.count (({ width := 7, code := 0x7cf7ebcf8efd39f2e1ab4e7cd86f5db7325ca92e9c376abd72b54911214078e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0403.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0403.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0403.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0403.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 65 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0403
    Papers.RationalityTen.SharedFrameCatalogue.group0403_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0213.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0213.count (({ width := 7, code := 0x7cf7ebcf8efd39f2e1ab4e7cd86f5db7325ca92e9c376abd72b54911214078e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0213.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0213.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0213.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0213.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 65 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0213
    Papers.RationalityTen.SharedFrameCatalogue.group0213_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0045.count (({ width := 7, code := 0x7cf7ebcf8efd39f2e1ab4e7cd86f5db7325ca92e9c376abd72b54911214078e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0045.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0045.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0045.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0045.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 65 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0045
    Papers.RationalityTen.SharedFrameCatalogue.group0045_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0043.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0043.count (({ width := 7, code := 0x7cf7ebcf8efd39f2e1ab4e7cd86f5db7325ca92e9c376abd72b54911214078e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0043.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0043.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0043.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0043.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 65 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0043
    Papers.RationalityTen.SharedFrameCatalogue.group0043_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x71070e70a7067026f86f36ef6e76e46bc6b169568167265c65164863a6355f95e55cf5b45a738c37435f3413372e12d52c22b02a928026024d22021b1a119b17a16d16412410a0e40a609e09c09b09a09609409008d08a08208007a07707406a06602b02802301d01c01601300e008007 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7377307227187107047036f76e76e06af6a868f67d66e65764e63c6296165d75c45b05985893613463323103052b92ae2a32972942652412301f81f218b1851701661621241050e00b40af0ad0ac0a80a40a109c09a09408e08a08207f07706e06a02b02802301d01c01601300e008007 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0940.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0940.count (({ width := 8, code := 0xe4e2e0dedcdbdad7d4d2cdcbc9c7c4c2c1bdbbb8b4b1b0adaa807d787371666462605f5c59554f4e42413e3d3c3b3a352e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0940.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0940.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0940.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0940.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0940
    Papers.RationalityTen.SharedFrameCatalogue.group0940_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0880.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0880.count (({ width := 8, code := 0xe4e2e0dedcdbdad7d4d2cdcbc9c7c4c2c1bdbbb8b4b1b0adaa807d787371666462605f5c59554f4e42413e3d3c3b3a352e2d2c2b2a292827262524232221201f1e0e0d0c0b0a0908070605 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0880.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0880.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0880.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0880.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0880
    Papers.RationalityTen.SharedFrameCatalogue.group0880_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0879.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0879.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0879.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0879.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0879.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0879.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0879
    Papers.RationalityTen.SharedFrameCatalogue.group0879_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0501.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0501.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0501.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0501.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0501.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0501.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0501
    Papers.RationalityTen.SharedFrameCatalogue.group0501_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0482.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0482.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0482.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0482.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0482.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0482.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame007_links_0000 record002_frame007_links_0064)
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0482
    Papers.RationalityTen.SharedFrameCatalogue.group0482_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0486.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0486.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0486.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0486.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0486.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0486.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame008_links_0000 record002_frame008_links_0064)
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0486
    Papers.RationalityTen.SharedFrameCatalogue.group0486_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0669.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0669.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0669.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0669.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0669.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0669.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame009_links_0000 record002_frame009_links_0064)
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0669
    Papers.RationalityTen.SharedFrameCatalogue.group0669_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
def record002_frame010_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0667.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0667.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0667.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0667.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0667.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0667.localPairCheck (smallEmbedding record002) (record002.maps 10)
      (record002.inverseMaps 10) record002_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame010_links_0000 record002_frame010_links_0064)
theorem record002_frame010_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 10 :=
  of_group record002 10 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0667
    Papers.RationalityTen.SharedFrameCatalogue.group0667_facts record002_frame010_indices record002_frame010_graph record002_frame010_links
def record002_frame011_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0668.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0668.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0668.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0668.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0668.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0668.localPairCheck (smallEmbedding record002) (record002.maps 11)
      (record002.inverseMaps 11) record002_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame011_links_0000 record002_frame011_links_0064)
theorem record002_frame011_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 11 :=
  of_group record002 11 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0668
    Papers.RationalityTen.SharedFrameCatalogue.group0668_facts record002_frame011_indices record002_frame011_graph record002_frame011_links
def record002_frame012_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0665.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0665.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0665.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0665.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0665.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0665.localPairCheck (smallEmbedding record002) (record002.maps 12)
      (record002.inverseMaps 12) record002_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame012_links_0000 record002_frame012_links_0064)
theorem record002_frame012_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 12 :=
  of_group record002 12 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0665
    Papers.RationalityTen.SharedFrameCatalogue.group0665_facts record002_frame012_indices record002_frame012_graph record002_frame012_links
def record002_frame013_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0666.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0666.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0666.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0666.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0666.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0666.localPairCheck (smallEmbedding record002) (record002.maps 13)
      (record002.inverseMaps 13) record002_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame013_links_0000 record002_frame013_links_0064)
theorem record002_frame013_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 13 :=
  of_group record002 13 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0666
    Papers.RationalityTen.SharedFrameCatalogue.group0666_facts record002_frame013_indices record002_frame013_graph record002_frame013_links
def record002_frame014_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0663.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0663.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0663.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0663.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0663.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0663.localPairCheck (smallEmbedding record002) (record002.maps 14)
      (record002.inverseMaps 14) record002_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame014_links_0000 record002_frame014_links_0064)
theorem record002_frame014_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 14 :=
  of_group record002 14 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0663
    Papers.RationalityTen.SharedFrameCatalogue.group0663_facts record002_frame014_indices record002_frame014_graph record002_frame014_links
def record002_frame015_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0664.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0664.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0664.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0664.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0664.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0664.localPairCheck (smallEmbedding record002) (record002.maps 15)
      (record002.inverseMaps 15) record002_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame015_links_0000 record002_frame015_links_0064)
theorem record002_frame015_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 15 :=
  of_group record002 15 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0664
    Papers.RationalityTen.SharedFrameCatalogue.group0664_facts record002_frame015_indices record002_frame015_graph record002_frame015_links
def record002_frame016_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0662.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0662.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0662.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0662.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0662.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0662.localPairCheck (smallEmbedding record002) (record002.maps 16)
      (record002.inverseMaps 16) record002_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame016_links_0000 record002_frame016_links_0064)
theorem record002_frame016_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 16 :=
  of_group record002 16 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0662
    Papers.RationalityTen.SharedFrameCatalogue.group0662_facts record002_frame016_indices record002_frame016_graph record002_frame016_links
def record002_frame017_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0028.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0028.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0028.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0028.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0028.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0028.localPairCheck (smallEmbedding record002) (record002.maps 17)
      (record002.inverseMaps 17) record002_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame017_links_0000 record002_frame017_links_0064)
theorem record002_frame017_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 17 :=
  of_group record002 17 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0028
    Papers.RationalityTen.SharedFrameCatalogue.group0028_facts record002_frame017_indices record002_frame017_graph record002_frame017_links
def record002_frame018_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0027.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0027.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0027.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0027.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0027.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0027.localPairCheck (smallEmbedding record002) (record002.maps 18)
      (record002.inverseMaps 18) record002_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame018_links_0000 record002_frame018_links_0064)
theorem record002_frame018_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 18 :=
  of_group record002 18 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0027
    Papers.RationalityTen.SharedFrameCatalogue.group0027_facts record002_frame018_indices record002_frame018_graph record002_frame018_links
def record002_frame019_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0386.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0386.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0386.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0386.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0386.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0386.localPairCheck (smallEmbedding record002) (record002.maps 19)
      (record002.inverseMaps 19) record002_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame019_links_0000 record002_frame019_links_0064)
theorem record002_frame019_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 19 :=
  of_group record002 19 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0386
    Papers.RationalityTen.SharedFrameCatalogue.group0386_facts record002_frame019_indices record002_frame019_graph record002_frame019_links
def record002_frame020_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0385.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0385.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0385.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0385.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0385.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0385.localPairCheck (smallEmbedding record002) (record002.maps 20)
      (record002.inverseMaps 20) record002_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame020_links_0000 record002_frame020_links_0064)
theorem record002_frame020_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 20 :=
  of_group record002 20 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0385
    Papers.RationalityTen.SharedFrameCatalogue.group0385_facts record002_frame020_indices record002_frame020_graph record002_frame020_links
def record002_frame021_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0383.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0383.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0383.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0383.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0383.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0383.localPairCheck (smallEmbedding record002) (record002.maps 21)
      (record002.inverseMaps 21) record002_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame021_links_0000 record002_frame021_links_0064)
theorem record002_frame021_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 21 :=
  of_group record002 21 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0383
    Papers.RationalityTen.SharedFrameCatalogue.group0383_facts record002_frame021_indices record002_frame021_graph record002_frame021_links
def record002_frame022_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0236.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0236.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0236.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0236.localPairCheck (smallEmbedding record002) (record002.maps 22) (record002.inverseMaps 22) record002_frame022_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0236.localPairCheck (smallEmbedding record002) (record002.maps 22) (record002.inverseMaps 22) record002_frame022_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0236.localPairCheck (smallEmbedding record002) (record002.maps 22)
      (record002.inverseMaps 22) record002_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame022_links_0000 record002_frame022_links_0064)
theorem record002_frame022_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 22 :=
  of_group record002 22 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0236
    Papers.RationalityTen.SharedFrameCatalogue.group0236_facts record002_frame022_indices record002_frame022_graph record002_frame022_links
def record002_frame023_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0235.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0235.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0235.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0235.localPairCheck (smallEmbedding record002) (record002.maps 23) (record002.inverseMaps 23) record002_frame023_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0235.localPairCheck (smallEmbedding record002) (record002.maps 23) (record002.inverseMaps 23) record002_frame023_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0235.localPairCheck (smallEmbedding record002) (record002.maps 23)
      (record002.inverseMaps 23) record002_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame023_links_0000 record002_frame023_links_0064)
theorem record002_frame023_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 23 :=
  of_group record002 23 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0235
    Papers.RationalityTen.SharedFrameCatalogue.group0235_facts record002_frame023_indices record002_frame023_graph record002_frame023_links
def record002_frame024_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0138.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0138.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0138.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0138.localPairCheck (smallEmbedding record002) (record002.maps 24) (record002.inverseMaps 24) record002_frame024_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0138.localPairCheck (smallEmbedding record002) (record002.maps 24) (record002.inverseMaps 24) record002_frame024_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0138.localPairCheck (smallEmbedding record002) (record002.maps 24)
      (record002.inverseMaps 24) record002_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame024_links_0000 record002_frame024_links_0064)
theorem record002_frame024_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 24 :=
  of_group record002 24 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0138
    Papers.RationalityTen.SharedFrameCatalogue.group0138_facts record002_frame024_indices record002_frame024_graph record002_frame024_links
def record002_frame025_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0214.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0214.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0214.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0214.localPairCheck (smallEmbedding record002) (record002.maps 25) (record002.inverseMaps 25) record002_frame025_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0214.localPairCheck (smallEmbedding record002) (record002.maps 25) (record002.inverseMaps 25) record002_frame025_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0214.localPairCheck (smallEmbedding record002) (record002.maps 25)
      (record002.inverseMaps 25) record002_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame025_links_0000 record002_frame025_links_0064)
theorem record002_frame025_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 25 :=
  of_group record002 25 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0214
    Papers.RationalityTen.SharedFrameCatalogue.group0214_facts record002_frame025_indices record002_frame025_graph record002_frame025_links
def record002_frame026_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0080.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0080.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0080.localPairCheck (smallEmbedding record002) (record002.maps 26) (record002.inverseMaps 26) record002_frame026_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0080.localPairCheck (smallEmbedding record002) (record002.maps 26) (record002.inverseMaps 26) record002_frame026_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0080.localPairCheck (smallEmbedding record002) (record002.maps 26)
      (record002.inverseMaps 26) record002_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame026_links_0000 record002_frame026_links_0064)
theorem record002_frame026_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 26 :=
  of_group record002 26 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0080
    Papers.RationalityTen.SharedFrameCatalogue.group0080_facts record002_frame026_indices record002_frame026_graph record002_frame026_links
def record002_frame027_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0079.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0079.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0079.localPairCheck (smallEmbedding record002) (record002.maps 27) (record002.inverseMaps 27) record002_frame027_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0079.localPairCheck (smallEmbedding record002) (record002.maps 27) (record002.inverseMaps 27) record002_frame027_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0079.localPairCheck (smallEmbedding record002) (record002.maps 27)
      (record002.inverseMaps 27) record002_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame027_links_0000 record002_frame027_links_0064)
theorem record002_frame027_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 27 :=
  of_group record002 27 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0079
    Papers.RationalityTen.SharedFrameCatalogue.group0079_facts record002_frame027_indices record002_frame027_graph record002_frame027_links
def record002_frame028_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0072.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0072.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0072.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0072.localPairCheck (smallEmbedding record002) (record002.maps 28) (record002.inverseMaps 28) record002_frame028_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0072.localPairCheck (smallEmbedding record002) (record002.maps 28) (record002.inverseMaps 28) record002_frame028_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0072.localPairCheck (smallEmbedding record002) (record002.maps 28)
      (record002.inverseMaps 28) record002_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame028_links_0000 record002_frame028_links_0064)
theorem record002_frame028_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 28 :=
  of_group record002 28 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0072
    Papers.RationalityTen.SharedFrameCatalogue.group0072_facts record002_frame028_indices record002_frame028_graph record002_frame028_links
def record002_frame029_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0101.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0101.count (({ width := 7, code := 0x1f3dfaf3e3bf6e9c786bd5a33e5c78afddb75ead4a54203f7aedd366ad19b262c172c569d325488d1213c68c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0101.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0101.localPairCheck (smallEmbedding record002) (record002.maps 29) (record002.inverseMaps 29) record002_frame029_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0101.localPairCheck (smallEmbedding record002) (record002.maps 29) (record002.inverseMaps 29) record002_frame029_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0101.localPairCheck (smallEmbedding record002) (record002.maps 29)
      (record002.inverseMaps 29) record002_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame029_links_0000 record002_frame029_links_0064)
theorem record002_frame029_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 29 :=
  of_group record002 29 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0101
    Papers.RationalityTen.SharedFrameCatalogue.group0101_facts record002_frame029_indices record002_frame029_graph record002_frame029_links
def record002_frame030_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0102.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0102.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0102.localPairCheck (smallEmbedding record002) (record002.maps 30) (record002.inverseMaps 30) record002_frame030_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0102.localPairCheck (smallEmbedding record002) (record002.maps 30) (record002.inverseMaps 30) record002_frame030_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0102.localPairCheck (smallEmbedding record002) (record002.maps 30)
      (record002.inverseMaps 30) record002_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame030_links_0000 record002_frame030_links_0064)
theorem record002_frame030_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 30 :=
  of_group record002 30 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0102
    Papers.RationalityTen.SharedFrameCatalogue.group0102_facts record002_frame030_indices record002_frame030_graph record002_frame030_links
def record002_frame031_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0056.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0056.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0056.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0056.localPairCheck (smallEmbedding record002) (record002.maps 31) (record002.inverseMaps 31) record002_frame031_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0056.localPairCheck (smallEmbedding record002) (record002.maps 31) (record002.inverseMaps 31) record002_frame031_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0056.localPairCheck (smallEmbedding record002) (record002.maps 31)
      (record002.inverseMaps 31) record002_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame031_links_0000 record002_frame031_links_0064)
theorem record002_frame031_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 31 :=
  of_group record002 31 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0056
    Papers.RationalityTen.SharedFrameCatalogue.group0056_facts record002_frame031_indices record002_frame031_graph record002_frame031_links
def record002_frame032_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0051.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0051.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0051.localPairCheck (smallEmbedding record002) (record002.maps 32) (record002.inverseMaps 32) record002_frame032_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0051.localPairCheck (smallEmbedding record002) (record002.maps 32) (record002.inverseMaps 32) record002_frame032_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0051.localPairCheck (smallEmbedding record002) (record002.maps 32)
      (record002.inverseMaps 32) record002_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame032_links_0000 record002_frame032_links_0064)
theorem record002_frame032_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 32 :=
  of_group record002 32 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0051
    Papers.RationalityTen.SharedFrameCatalogue.group0051_facts record002_frame032_indices record002_frame032_graph record002_frame032_links
def record002_frame033_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0059.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame033_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0059.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame033_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0059.localPairCheck (smallEmbedding record002) (record002.maps 33) (record002.inverseMaps 33) record002_frame033_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame033_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0059.localPairCheck (smallEmbedding record002) (record002.maps 33) (record002.inverseMaps 33) record002_frame033_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame033_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0059.localPairCheck (smallEmbedding record002) (record002.maps 33)
      (record002.inverseMaps 33) record002_frame033_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame033_links_0000 record002_frame033_links_0064)
theorem record002_frame033_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 33 :=
  of_group record002 33 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0059
    Papers.RationalityTen.SharedFrameCatalogue.group0059_facts record002_frame033_indices record002_frame033_graph record002_frame033_links
def record002_frame034_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0036.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0036.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame034_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0036.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame034_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0036.localPairCheck (smallEmbedding record002) (record002.maps 34) (record002.inverseMaps 34) record002_frame034_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame034_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0036.localPairCheck (smallEmbedding record002) (record002.maps 34) (record002.inverseMaps 34) record002_frame034_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame034_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0036.localPairCheck (smallEmbedding record002) (record002.maps 34)
      (record002.inverseMaps 34) record002_frame034_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame034_links_0000 record002_frame034_links_0064)
theorem record002_frame034_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 34 :=
  of_group record002 34 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0036
    Papers.RationalityTen.SharedFrameCatalogue.group0036_facts record002_frame034_indices record002_frame034_graph record002_frame034_links
def record002_frame035_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0047.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0047.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame035_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0047.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame035_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0047.localPairCheck (smallEmbedding record002) (record002.maps 35) (record002.inverseMaps 35) record002_frame035_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame035_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0047.localPairCheck (smallEmbedding record002) (record002.maps 35) (record002.inverseMaps 35) record002_frame035_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame035_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0047.localPairCheck (smallEmbedding record002) (record002.maps 35)
      (record002.inverseMaps 35) record002_frame035_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame035_links_0000 record002_frame035_links_0064)
theorem record002_frame035_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 35 :=
  of_group record002 35 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0047
    Papers.RationalityTen.SharedFrameCatalogue.group0047_facts record002_frame035_indices record002_frame035_graph record002_frame035_links
def record002_frame036_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0048.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0048.count (({ width := 7, code := 0x12a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame036_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0048.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame036_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0048.localPairCheck (smallEmbedding record002) (record002.maps 36) (record002.inverseMaps 36) record002_frame036_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame036_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0048.localPairCheck (smallEmbedding record002) (record002.maps 36) (record002.inverseMaps 36) record002_frame036_indices (Fin.ofNat record002.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record002_frame036_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0048.localPairCheck (smallEmbedding record002) (record002.maps 36)
      (record002.inverseMaps 36) record002_frame036_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record002_frame036_links_0000 record002_frame036_links_0064)
theorem record002_frame036_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 36 :=
  of_group record002 36 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0048
    Papers.RationalityTen.SharedFrameCatalogue.group0048_facts record002_frame036_indices record002_frame036_graph record002_frame036_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (Fin.cases (record002_frame010_supported hcells) (Fin.cases (record002_frame011_supported hcells) (Fin.cases (record002_frame012_supported hcells) (Fin.cases (record002_frame013_supported hcells) (Fin.cases (record002_frame014_supported hcells) (Fin.cases (record002_frame015_supported hcells) (Fin.cases (record002_frame016_supported hcells) (Fin.cases (record002_frame017_supported hcells) (Fin.cases (record002_frame018_supported hcells) (Fin.cases (record002_frame019_supported hcells) (Fin.cases (record002_frame020_supported hcells) (Fin.cases (record002_frame021_supported hcells) (Fin.cases (record002_frame022_supported hcells) (Fin.cases (record002_frame023_supported hcells) (Fin.cases (record002_frame024_supported hcells) (Fin.cases (record002_frame025_supported hcells) (Fin.cases (record002_frame026_supported hcells) (Fin.cases (record002_frame027_supported hcells) (Fin.cases (record002_frame028_supported hcells) (Fin.cases (record002_frame029_supported hcells) (Fin.cases (record002_frame030_supported hcells) (Fin.cases (record002_frame031_supported hcells) (Fin.cases (record002_frame032_supported hcells) (Fin.cases (record002_frame033_supported hcells) (Fin.cases (record002_frame034_supported hcells) (Fin.cases (record002_frame035_supported hcells) (Fin.cases (record002_frame036_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))
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
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x7307236e469968f5d75875294c649d49247e46745845244c44743c41e4073fb3d73cb37b36931930d2ad29b27f26c25924423c2361c51aa19516f16c1330fb0f80d50c50c10bf0bd0b70b60ad0a109407106805f05805605204f04c04404103803102802201f01c00e00d009007002001000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0909.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0909.count (({ width := 9, code := 0xdeecf63acd5e9b257cbbd9abb4da4cd6632d8ac461b0a7b3cdd4da692a51689401f8c6612c158a24f2692c92482311086421d0e46e36178ac4c230f870240d0502410070200c0401 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ record007_frame001_links_0000
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0909
    Papers.RationalityTen.SharedFrameCatalogue.group0909_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0909.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0909.count (({ width := 9, code := 0x68f3196c05ead358ab5469f4a9b4ba250b7a395c6de6e3459ca852a2d12803f18cc2582b1249041200fc7a3a1c8dc6c351a0cc642e15098461f0e06c34190c0481a0a048200e04018080200 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0909
    Papers.RationalityTen.SharedFrameCatalogue.group0909_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0909.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0909.count (({ width := 9, code := 0x562ad51a7d16833d9ccc65d158943616f67a395c6de6e3499ca952a2d12803f18cc2582b1249041200e872371b0d46833190c4602f170b4582b15098461f0e06c34190c0481a0a048200e04018080200 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 71 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0909
    Papers.RationalityTen.SharedFrameCatalogue.group0909_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0675.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0675.count (({ width := 8, code := 0x817170605f525141403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a2928272625211f1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0675.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0675.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0675.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0675.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0675
    Papers.RationalityTen.SharedFrameCatalogue.group0675_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0xf45e03b56c6d4d98326640c5d7bae059eb2d5ea844e29291ea0b3f2790f09d63986e8db19a326590a814a27c4748b90a2003ac730b816227c478820e01bc340660b21542704c09011c2304406e0d41782b0480880f01d0380580780d0120200380400600800800 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x23b8ea3883207785dc741c26ddb1681955d16f5393e4e5334b92247517419013c0ed354cf30cc02c8ad26092214801c86f19859160501384d12c4a124471003a0d8350d0320b42b098250801e0701b0681604c0f034090200700c0200400 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0x74b5988bfddee16cb55a2cd5dadcfe7b399bc6e330f86c2a11017ebd9cee16934578b755a9d3094409f0de6b2f168a84b2512490411e0e06833190c4602f170b4582b1489c482310078381b0d058260f068241007018080200 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0524.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0524.count (({ width := 9, code := 0x57e7f238ec662d1489c462108833b5d6ea7433d9ac56230982bd5d2d554a64da691a89409f8ea7232984b256269288e42209007e381a8cc5e2e168b0562a148a04e261208842200f874361a0c858260f068241007018080200 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0524.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0524.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0524
    Papers.RationalityTen.SharedFrameCatalogue.group0524_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0612.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0612.count (({ width := 9, code := 0x562af56a9d428f3a9bc92411b85401f4ea7335da4c55eae16aaf56a99449a4c255228c452210c84401f0de6d3298cbc5c2713496452210c8441200f07033190b4582b13090401f0d06430150a048200c058240e06018080200 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0612
    Papers.RationalityTen.SharedFrameCatalogue.group0612_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x1009d1b6f6b2d259eb36650c818e307600bdd78aba560a954e26d4ca9552723946a8b90f2154127d4f79e23826acc895d29c524a093c24c4787b0ec1b0340628c01762503c0690ba1482704d09812c250490901181f83906c0d01682b04a0880f01d0380580980f01a0240400700600800800 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xc6784effd6799b22e3345c8690aa0cb725fab2157aaa518a1d2d246458840ff1f838e6f0d518e2f659c9c92e2323fc768db128240440851062003f07c0c6158290510a01381882203c0740e01b03005c0a81001a0240400700600800800 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x118e890442a03cfb67d23c81df4ed67593a51d0ce447133839bb0dc06cc3571a7cd1067a3319960a484ff27393509784b223f11848ae43921790987ea3e71ed8cdc6242f71728b2857e287135098048823a11887fc3e41e50c805b42c80c802e016c0b405702b01540a6052027812008c04301e80ec070024011808803e01e00e803c01c00d00500240100040018008002000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x1b235169ac9d8b3125f4bc5742e15bcb6d6aacf598b095fab8562ab954aa6542a7120a344548910d2174087e0fa1e93ca788e79c9386614b99652ba53ca593b25e4a48f91922a40c7e0f519a2f45d07208c114220410800fc1e83c0760e41b8350640c41802104007c0e01b03403c0700d0140240400400600800800 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record029_frame002_links_0000 record029_frame002_links_0064)
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4e4da221501e7db3e91e48eb274a3a19c4cdd86cc304176cb6a4ff26a12c88ae42f2130fdc78c3b41ce8e306ea3671890c145ca2d815f8a244d826012308e84622010da066c3201780b6859026208d04601a80d205b02d015c0ac05502a014c0a404f023010c064031011808803e01e00e807003201700a003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x64958354553e52952251c51550d5065014f14e84e44c94b449946c46443642d3e43c539038835534c30c2f72e92d82d02c92bd2b62b02ab26f25824722f2172041dd1d31ba18515f15812c10c0e60d80c80c40c106f06b05f05b05505405305204e04c04804603d03703302c02702302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x9711ba0cc0279af15d83ab74ce81ccb96722e25c1b796a6cad8b30f5d6b7d5e2b553a9e12c24d48e8f11aa314587fcf79e13906d8d899531c604af94d256494810e419a31c5d8a914423c4606d0d21782d8550a814c2904e09811c2283e0720dc1982c04e0941181d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x77e7736866495bb58354553e52f52952251c51550d5065014f24e94de49946c4644133e43c539038835e30c2f72e92d82d02c92b62b02ab26f2582472212092041dd1d31ba18516d15f15812c10c0ed0e60d80c80c40c10a709d08d06f06b05f05b05505405305204e04c04704503d03703403302c02702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x31a614c1781afe5f0b6b632b4d36a0133e2c42684304601bba71adb9a03165f4abd4627e4f29d12d2524888b10f20e354654c597b2dc590ae9192083f0768e01b034c580a61062084007f0fa1e03a0680ca16c2c0530a2140270490860d4190270460780e81c0360540800800e00800800 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6f26ce6a669a68f67e61a5df5aa57053a50349546946445043f3ce3963633262ef2bd26523822a21e2162071fe1ef1e01cd1bc16b15c15414913f13613210c0fe0f60ed0e50de0da0c60be08e08d08a08908708207d06d06905e05a05505305205004c04503603202702301e01d01c01b015010008007002001000 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3381994cb064eb10164ea71511a84133e8f745622690607e93db9df0ed270c2f994f49de4dc2358f0c6f036617e0ad450625212588bc3e018e0b5859024a10207d83981be0d8069024811a08c045822810c07d03781a80d206002d81680ae05602a81500a6052027011406e03201880a004602200f807803a01c } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x4b891317a0a3f97e0eedd539f700dd5b5356694c5160aa24b895121a384507fcf99e83c6760d317c28e4d08c9052003a06e0d518c3045d0a31222403e0750da194308600bc1642904f09a1302103d0680c41802d04a0880f81d0380480700d0140240400700800800800 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6666625a259e50b5074c949e47f46445a44443242c3ed3b83a93a63a236e33b32e32c32a2ec2ce2b629b28e28926c26122c22120f20a2061ec1d01b919117414b1361251060ee08107f07e06906406305a05505405105004f04e04d04c04704404203703203102802302201f01e01d01c01a01801300e00d00a009008007004003002001000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe3d47b21450608113f81f9cfaa7c43bc1cb8e447153829ab0d3c66a32598f4c125f82b7954ca344fe27492d08d045a22810e485642120d0e2c6d832b1860bc056a25b12508f444221010187e83481770a304981d20ca063817c0b605802a81500a60510270130094048023011007a037019809c04602000e807002400e005802000e0050018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x5ca81cf6de5bbc758e9dd23a172ee25bf3766e2d65a9b40662cad8c30c5a6b11532944fa9912223a46e8a50fa1942876ce49af340624b814e2884f898927248480820f21b2320598a714a1702c0550a41442804e0981282484708a1101e83706609c1182003a0700900e0160200380500600800800 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6f55a15474e148a47e47146c46145643a4214173f83ee3c73bd3ac38e3803623473313133032ec2bc2ac2a829f29a29729423c22f2081fc1f01d51b018f18317d16a16616213a11b0f00dc0ca0ba0aa09f09906a05d05905305205104f04c04a04804504203c03703403302d02a02702301d01c01201000e00b008007003002001000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
def record048_frame002_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0573.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0573.count (({ width := 9, code := 0x65ebb499c4aa4f239047a3b188a4460f067ebe9eaed74389bedb6a34592be5dae16ab358abd48a14ea69309046a1506803e1e8f07236994bc5c2b93c92471a8c4602d160ac54291409c4c25110803c1d0c8602e1508840180b050200c05018080200 } : Fields).get c.val)
theorem record048_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record048_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record048) (record048.maps 2)
      (record048.inverseMaps 2) record048_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record048_frame002_links_0000 record048_frame002_links_0064)
theorem record048_frame002_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 2 :=
  of_group record048 2 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0573
    Papers.RationalityTen.SharedFrameCatalogue.group0573_facts record048_frame002_indices record048_frame002_graph record048_frame002_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (Fin.cases (record048_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0575.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0575.count (({ width := 9, code := 0x6c759a7d1e7f3591bad7eb34da14c259289147e39157cb99c2d9683057ebc5bad968b15729544a14b2551a8c431fcfa7737988b25627924904622908803f1c8d4662f170b44e210f06430170a048200f0682c1007018080200 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0575.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0575.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0575.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0575.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0575
    Papers.RationalityTen.SharedFrameCatalogue.group0575_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0573.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0573.count (({ width := 9, code := 0x4e657228fc7a3b1c8c452230e864220d0380bf5f4f679bb1cee26fb79a8d16732d94c3602f976b9582b93a9a4c255249146a2d108541a04fe793b9c8da6832970a830178b85a2b150a44c251208842200c8602a1409044160a048200e06018080200 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0573
    Papers.RationalityTen.SharedFrameCatalogue.group0573_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
def record051_frame002_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0567.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0567.count (({ width := 8, code := 0x9f9d9a99989796959392908f8c8b8988868582817e7b787675706f6e6d6c6867666564605f54535251504f4d4c4b4a4948474544403e3c3b39372a29282725242321201f1d1c1b15141211100f0b0a0908070603020100 } : Fields).get c.val)
theorem record051_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0567.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0567.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0567.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record051_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0567.localPairCheck (smallEmbedding record051) (record051.maps 2)
      (record051.inverseMaps 2) record051_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record051_frame002_links_0000 record051_frame002_links_0064)
theorem record051_frame002_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 2 :=
  of_group record051 2 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0567
    Papers.RationalityTen.SharedFrameCatalogue.group0567_facts record051_frame002_indices record051_frame002_graph record051_frame002_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (Fin.cases (record051_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x405805001f93d2772e9dcf39470edddaf35467eced8bb0b60abfd6f2db58ea8143a764da98929a484668b50f21a3fc7d0f89ed3a6718d69842704648a0e91a82e0588971262383e87c0f61e83b8720d41903185f0b815c2b0520a21402784d09210c1c0320620ac140230440780e81c } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
def record054_frame002_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x3e17baf69e4ba4708dc9b3b5e6a4d0d99b2d63ac6d7e2f35dcba965ac856aa4538a614aa92920a3143885502a023cc77ced9d83706b0cc17424c4087d0dc19a2d0568971222343b8760ea1d03886c0c61742e0580aa1402784b094124240470880f81b03005e0ac140230440780e81c } : Fields).get c.val)
theorem record054_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record054_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record054) (record054.maps 2)
      (record054.inverseMaps 2) record054_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record054_frame002_links_0000 record054_frame002_links_0064)
theorem record054_frame002_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 2 :=
  of_group record054 2 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record054_frame002_indices record054_frame002_graph record054_frame002_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (Fin.cases (record054_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xc7955faaa9538a1548d24290ce857421a038cc064b31f18b8c125af2a81494a124fc26192608f846f22f90fc7a43bf1a68cc05fc2ed16e8ab051e25d12608f03de1df0e4868831615709d84c41fc0f4054823411806c03501a40c005b02d01580aa054029813806803201880bc05a02a014008c04401e00e8070032013008003801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0714.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0714.count (({ width := 9, code := 0x34596c0daebb4aa24da572591c761d0b82c09faf774395bedc69b1580bd5d2dd6aab50a28f87a3a9ccd66832988b4592b154a04e261289047231148441200fc74391c0dc5a2c158a85228130944823110843e1e0e8702811050241007028100602 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0714
    Papers.RationalityTen.SharedFrameCatalogue.group0714_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1ba0d235b5aaf938e9964a123f11c08d9314969ca9a52b27a12648ce4322008fc477433816f0af050a22a0fc070c3241820a384582120fc07a83881b80d606802bc15c0a704d824411a08c04582100f006e03501a408003601900c405c027012808c04401f00f0074038019009004001c00d0050024010007 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
def record066_frame001_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x169c9b4442a08101e7ec3ed9f48f567923661ab8c105db2da96909fe4d425911908ae43c21790988123f71e30c485ca2bf136898048e23a118884c40219c0c805e42da1640a204c413008d04601d40d4069033016c0b405802b81580aa054029811808603d01900c405c023011008003e01e00e807003200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record066_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record066_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record066) (record066.maps 1)
      (record066.inverseMaps 1) record066_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record066_frame001_links_0000 record066_frame001_links_0064)
theorem record066_frame001_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 1 :=
  of_group record066 1 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record066_frame001_indices record066_frame001_graph record066_frame001_links
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (Fin.cases (record066_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x169c9b447ea36d148885422a03cfb67d23d51e48d5a6953381978c145dd2da9690a204f426492c8920480237115c88c42f21310207ee3c61910c185b22bf14d0a244ea26012788e846221210086703201790b685902620fb04682300d406903301740b605a02b81580aa05402980f807803901900c405c025011808803e01e00e80700320100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record067_frame001_links_0000 record067_frame001_links_0064)
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33294209fa48e23e918289a431a0c0ff67e93e39edc9b84c61f40f1871a3661978bf058e2b51498a0c49824511b88c044420e0ff87e43e61e40ef07403821ba0d9869833c1910c505ec2ea15f0ac052828813d09a84bc25012108603c011a08c04581a80d206602e816c0b405702b01540a805301900c405c025011808803e01e00e807003601a00c806002a0100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
def record068_frame002_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2d393689a147ea36d148885422a03cfb67d23d51e48b6a5a428813d09924b2240115c85e4262040fdc76a3a91c68e046da34f1910c5060c2e716c8afc53828913b89804a223a11888484021d50e2869c3381900c205e42da16409883ec11a08c04581a80d206602e816c0b405702b01540a805301900c405c025011808803e01e00e807003601a00c806002a0100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record068_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record068_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record068) (record068.maps 2)
      (record068.inverseMaps 2) record068_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record068_frame002_links_0000 record068_frame002_links_0064)
theorem record068_frame002_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 2 :=
  of_group record068 2 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record068_frame002_indices record068_frame002_graph record068_frame002_links
def record068_frame003_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6b35e55dd56c5555305194f84da4b24a549348d3c33bc35734832d31b3022ed2cf2c62b82b429b29328427826424423822f2262112091f41e31dd1d41c41b61a519918b18717116615414613a12d11f1131070eb0c508108007f06406306005905705605305205105004f03203102e02502302201f01e01d01c01b01a01901801501000e00d00a009008007005004003002001000 } : Fields).get c.val)
theorem record068_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record068_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record068) (record068.maps 3)
      (record068.inverseMaps 3) record068_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record068_frame003_links_0000 record068_frame003_links_0064)
theorem record068_frame003_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 3 :=
  of_group record068 3 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record068_frame003_indices record068_frame003_graph record068_frame003_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (Fin.cases (record068_frame002_supported hcells) (Fin.cases (record068_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
def record069_frame001_indices (c : Fin record069.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x169caae4da268510a8204079fb0fb67d23d59e48d5c5b52d212c88c845721e10bc84c4091fb8ed475238d1c08db46282e715f8ac053827713689804a224711d08c44262010ea871434e19c0c806102f216d0b20510262098046823011607503501a40cc05b02d01600ae05602a81500a603d01900c405c023011008003e01e00e807003601a00c806002a00e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record069_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record069.data.requiredEdges q = true := by decide +kernel
theorem record069_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record069) (record069.maps 1) (record069.inverseMaps 1) record069_frame001_indices (Fin.ofNat record069.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record069_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record069) (record069.maps 1) (record069.inverseMaps 1) record069_frame001_indices (Fin.ofNat record069.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record069_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record069) (record069.maps 1)
      (record069.inverseMaps 1) record069_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record069_frame001_links_0000 record069_frame001_links_0064)
theorem record069_frame001_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) : Supported record069 1 :=
  of_group record069 1 (smallEmbedding record069) (small_cells_exact record069 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record069_frame001_indices record069_frame001_graph record069_frame001_links
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (Fin.cases (record069_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcca64f2c4150ca3750826392128ac44d2028ff47e93b51770aa450326e11687aa3781b30b5858c2b5126091447023110688183ca1dd0eb07403901b90d986b432018a0c105f02b01510a504f425c12108c84301de0e9046823011608503f01c00d4069030016c0b405602a81500a604d02300e0064031014008c04401e00e807003601a00c8060028013008803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (smallEmbedding record074) (small_cells_exact record074 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
def record074_frame002_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7076fc68664661c6085db59b56955d52852251d4ef47342b4003ee3ba37233f3352ff2f92f42c22b82a929c26325722621820b1fc1f11e11d71d01a819f19018815414d14313511e10b0fc0ec0c60c108708608508107c06e06806705e05905805405305205104b04403703103002802302201e01d01c01b01a01901801401301100e00d00b009008007004003002001000 } : Fields).get c.val)
theorem record074_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record074) (record074.maps 2) (record074.inverseMaps 2) record074_frame002_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record074) (record074.maps 2) (record074.inverseMaps 2) record074_frame002_indices (Fin.ofNat record074.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record074_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record074) (record074.maps 2)
      (record074.inverseMaps 2) record074_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record074_frame002_links_0000 record074_frame002_links_0064)
theorem record074_frame002_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) : Supported record074 2 :=
  of_group record074 2 (smallEmbedding record074) (small_cells_exact record074 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record074_frame002_indices record074_frame002_graph record074_frame002_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (Fin.cases (record074_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x12964c4638ad08dfd3db7a8ecdc93656bed65a333d660ca58d3135a6b0951a885069f92ba2241c814f09d2398718b715e29451c9492423c41c768d61762a05209f138234408800fa1dc3786e0ce1943085c0b21602b8530a41001e8380660c4148270460881001d0380480780e01a0280400700600800800 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
def record078_frame001_indices (c : Fin record078.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x7aaf0dc1b72652c5577ade4d896527a4a4808c11321a4067d4f51e039a66cc71892ec584ab95027449c8f9191c43706c0cd18a2fc3e8760e01b83686c0ca17c2e85c0b614c2804f09c12c2504909011c200360660c81882f05a09c1202304407c0f01d0380640a01201e0380680a0120200380400600800800 } : Fields).get c.val)
theorem record078_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record078.data.requiredEdges q = true := by decide +kernel
theorem record078_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record078_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record078_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record078) (record078.maps 1)
      (record078.inverseMaps 1) record078_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record078_frame001_links_0000 record078_frame001_links_0064)
theorem record078_frame001_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) : Supported record078 1 :=
  of_group record078 1 (smallEmbedding record078) (small_cells_exact record078 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record078_frame001_indices record078_frame001_graph record078_frame001_links
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (Fin.cases (record078_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
def record080_frame001_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x32c9878a4d4eba6792a4945497a46d21890647fa3a8f707963711a04c8262c2df14e89e64d1254926490a46722110c884640f1f88ef469e2cb142098847422a10b07e03a61c30da068030413a099847822e10a08203a416a08d04601a80d2066030816c0b405702b01540a805302300f807803501900c405c029011808803e01e00e80700320140070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record080_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record080_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record080) (record080.maps 1)
      (record080.inverseMaps 1) record080_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record080_frame001_links_0000 record080_frame001_links_0064)
theorem record080_frame001_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 1 :=
  of_group record080 1 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record080_frame001_indices record080_frame001_graph record080_frame001_links
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (Fin.cases (record080_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
def record081_frame001_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6652a194209fa4c7a42518089a431a0c10187fb3f49edcaa44dc263116c7aa38c1b30cbc5f82d81638ad450624c12288e045220d10307943ba1d00e086e83661a60cb86443141820ba857c2b014a0a204f425012108c844c2180f0046823011607e03501a40cc06102d81680ae05602a81500a604601900c405c029011808803e01e00e807003601a00c80600280110070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record081_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record081_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record081) (record081.maps 1)
      (record081.inverseMaps 1) record081_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record081_frame001_links_0000 record081_frame001_links_0064)
theorem record081_frame001_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 1 :=
  of_group record081 1 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record081_frame001_indices record081_frame001_graph record081_frame001_links
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (Fin.cases (record081_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x7bcef1bd36a652c5587af85c6b616329d538a613ca634a893d2523044c869019fe3f47d0ed1d4390700d919b31c5d8b09572a0528a31392684b88a1041fc3886e0d819a3145f8bb130250488740da1b03085c0b61402784e0941242404707e0f01c0320620bc168240460881081e03a0700c81401e0380680b0120200380400600800800 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
def record083_frame001_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994b865b1aa214209fa4c7a301134873431a13d06080c3fd9fa4f6e65231795509b84c622d8e306cc33f1978c6c5f82d81638ad450624c12288e04521f90ee874038e1ba0d3067c32e1910c5060c2ea15f0ac052828813d094048422610c07b03c011a08c04581d80e806a03481980c205b02d015c0ac05502a014c07c03c01900c405c029011808803e01e00e807003601a00c806002800e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record083_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record083_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 1)
      (record083.inverseMaps 1) record083_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record083_frame001_links_0000 record083_frame001_links_0064)
theorem record083_frame001_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 1 :=
  of_group record083 1 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record083_frame001_indices record083_frame001_graph record083_frame001_links
def record083_frame002_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0600.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0600.count (({ width := 11, code := 0x1ee3be772e29b43626a8c65863015f8bdd762e15b6b5d64a915189751d2354487acef1d63a4734e21b936a6c0d1994320624c115f28c4e49a92923c4648890d21240c7b8e41be344668c71782e0568a612a2483786e0da19c3305e0ba1702c0530a413c2704d09812c1d8390600bc168290460880f81e03a0700d81a0320600a00e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record083_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record083_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record083) (record083.maps 2)
      (record083.inverseMaps 2) record083_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record083_frame002_links_0000 record083_frame002_links_0064)
theorem record083_frame002_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 2 :=
  of_group record083 2 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0600
    Papers.RationalityTen.SharedFrameCatalogue.group0600_facts record083_frame002_indices record083_frame002_graph record083_frame002_links
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (Fin.cases (record083_frame001_supported hcells) (Fin.cases (record083_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x30f13ae9c14dd26b533c96e4a9251526c92f494246d21890647fa3a8c826193031788b7c53c2799344956499243919c8844322118fc47543971b98d3c59a28413108f04542180fc074c3861b40c104e826612c08f045c22010a08203bc1d20ae046823011606a03481a00ce06603281840b605a02b81580aa05402980c806203001780b805a029011808803e01e00e807003601a00c806002800e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame001_links_0000 record084_frame001_links_0064)
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
def record084_frame002_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33294209eb4ec26d531e90b46022690ea863428a0c10187fb3f49edc9b84b725212048b63d71c60d9868232f18e8bf05b02c715a8a0c49824511c08a43f21dd0e807043741b30d3065c32218a0ba851027a136094048423411308603dc1e00ae046823011606a03481a00ce06603281840b605a02b81580aa05402980c806203001780b805a029011808803e01e00e807003601a00c806002800e0068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record084_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 2) (record084.inverseMaps 2) record084_frame002_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 2) (record084.inverseMaps 2) record084_frame002_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 2)
      (record084.inverseMaps 2) record084_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame002_links_0000 record084_frame002_links_0064)
theorem record084_frame002_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 2 :=
  of_group record084 2 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record084_frame002_indices record084_frame002_graph record084_frame002_links
def record084_frame003_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xcf14fa94522a3142a714ca9812ca564a693923a454848e4cc98e316618bf96b2be568a995029a520a093f2784cc9292223a458810f61e23a8738e41be3606b0d31942f45e0bb1722e05b8b616a2c8588a8112220438680ce198328640c617c2c8580aa150298520a20c81883005e0b8168290460880f81e03a0700d81a0320600a00e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record084_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record084) (record084.maps 3) (record084.inverseMaps 3) record084_frame003_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record084) (record084.maps 3) (record084.inverseMaps 3) record084_frame003_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record084) (record084.maps 3)
      (record084.inverseMaps 3) record084_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame003_links_0000 record084_frame003_links_0064)
theorem record084_frame003_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 3 :=
  of_group record084 3 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record084_frame003_indices record084_frame003_graph record084_frame003_links
def record084_frame004_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x13ce3e4738db1a630c31822ff9f6be27b0f21db3aa744e1d77ae75c4b7d6c2b552ea153c26e4cc9612423e46a870ff9fa3e87b0e21a632a620be9772d2574aa14e2744147f8f91d63946f0d51962b8530790d61a83485a0b21602b8560aa14c2684c0921202384608a0c01782e05a0b0158290460880f81e03a0700d81a0320600a00e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record084_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record084) (record084.maps 4) (record084.inverseMaps 4) record084_frame004_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record084) (record084.maps 4) (record084.inverseMaps 4) record084_frame004_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record084) (record084.maps 4)
      (record084.inverseMaps 4) record084_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame004_links_0000 record084_frame004_links_0064)
theorem record084_frame004_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 4 :=
  of_group record084 4 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record084_frame004_indices record084_frame004_graph record084_frame004_links
def record084_frame005_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0xef1b53616b8d61a9334638c3d832ff5f2bbd722de5b0b1d2a24d4949192122641a7f8fa9ee3d4780ea9cd3906cccc195324638b81572945049d13524e47c8c9141fe34c668c917e2ec5b0b01562644a87c0da1b03585c0b61682c8580ae1542784e0961282484808e0c81883005e0b8168290460880f81e03a0700d81a0320600a00e01a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record084_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record084) (record084.maps 5) (record084.inverseMaps 5) record084_frame005_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record084) (record084.maps 5) (record084.inverseMaps 5) record084_frame005_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record084) (record084.maps 5)
      (record084.inverseMaps 5) record084_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame005_links_0000 record084_frame005_links_0064)
theorem record084_frame005_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 5 :=
  of_group record084 5 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record084_frame005_indices record084_frame005_graph record084_frame005_links
def record084_frame006_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0605.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0605.count (({ width := 10, code := 0x339bc2e8b96e1b72c2ab2a1a5e8da2a7f9c66a992527e1ef7ade8791c66d5a967198631825e5715b15a5093e4ed364891342905404fc3d8ed3a4e4364bf2f4b92c4ac2a8a528493238761a46819c561545414c521444e1204711043108411002f0b82d0b02b0a827084200741c06c1a0641805c160500e0340a0240801c060140400c0200400 } : Fields).get c.val)
theorem record084_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0605.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record084) (record084.maps 6) (record084.inverseMaps 6) record084_frame006_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record084) (record084.maps 6) (record084.inverseMaps 6) record084_frame006_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0605.localPairCheck (smallEmbedding record084) (record084.maps 6)
      (record084.inverseMaps 6) record084_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame006_links_0000 record084_frame006_links_0064)
theorem record084_frame006_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 6 :=
  of_group record084 6 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0605
    Papers.RationalityTen.SharedFrameCatalogue.group0605_facts record084_frame006_indices record084_frame006_graph record084_frame006_links
def record084_frame007_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0603.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0603.count (({ width := 9, code := 0x405eaf3793c5e0ea73389c0df6eb6daed66a3457ebd5e2ed74b4582b154a953a9542a04f26d269248a41148641200fe7d3d9dcec7438998ca6431184c05f2f16cb457289409e492411c8c4522108783b1c0dc6c351a0b85a2c158a85227108803a1c0d86832180b858280e068281208038180a04018080200 } : Fields).get c.val)
theorem record084_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0603.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0603.localPairCheck (smallEmbedding record084) (record084.maps 7) (record084.inverseMaps 7) record084_frame007_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0603.localPairCheck (smallEmbedding record084) (record084.maps 7) (record084.inverseMaps 7) record084_frame007_indices (Fin.ofNat record084.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record084_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0603.localPairCheck (smallEmbedding record084) (record084.maps 7)
      (record084.inverseMaps 7) record084_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record084_frame007_links_0000 record084_frame007_links_0064)
theorem record084_frame007_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 7 :=
  of_group record084 7 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0603
    Papers.RationalityTen.SharedFrameCatalogue.group0603_facts record084_frame007_indices record084_frame007_graph record084_frame007_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (Fin.cases (record084_frame002_supported hcells) (Fin.cases (record084_frame003_supported hcells) (Fin.cases (record084_frame004_supported hcells) (Fin.cases (record084_frame005_supported hcells) (Fin.cases (record084_frame006_supported hcells) (Fin.cases (record084_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x817bcedbc6d976c1b559a22cc96282afd532a38507a4b12368ad44ca130fa67c53db1e9ce3858b2b294109b63f81f38de46ca31814f8a445042730ef075c39e1b90d686602e816e0a884f425011208283bc1d20cc05c028c12e09104802300fe06e03601a40be05c02d01580aa05402380d8068031013809004401e00e8070032012008003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
def record089_frame001_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x663af1d70ea0d4fd242501a7fb3f41f20f6e7a6349994c9b24c61ea8b6458e2b414a0a0c4e424c122888c41a2060f287203821980c8862430417c0ba85b42be1580a5051027a12f094046422610c071026c13008c04581f80f007503481980be05b02d01600ae05502a014c08c04001e80c405c027011808804001f00e807003601a00c8060024011007003401600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record089_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record089_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record089) (record089.maps 1)
      (record089.inverseMaps 1) record089_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record089_frame001_links_0000 record089_frame001_links_0064)
theorem record089_frame001_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) : Supported record089 1 :=
  of_group record089 1 (smallEmbedding record089) (small_cells_exact record089 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record089_frame001_indices record089_frame001_graph record089_frame001_links
def record089_frame002_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xab1a57a3994b94089579678176d74272b71369f6835b65ad51945944a43c41d40f3fd3d73cb39636935630c2c62b62652552452332252152021e11d41c31b51a81871781561451350dc09909608c08b07e07807506906605f05b05a05805705505405304604003d03102e02702302202001f01d01c01b01a01901801201100e00d00b00a008007005004003002001000 } : Fields).get c.val)
theorem record089_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record089) (record089.maps 2) (record089.inverseMaps 2) record089_frame002_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record089) (record089.maps 2) (record089.inverseMaps 2) record089_frame002_indices (Fin.ofNat record089.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record089_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record089) (record089.maps 2)
      (record089.inverseMaps 2) record089_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record089_frame002_links_0000 record089_frame002_links_0064)
theorem record089_frame002_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) : Supported record089 2 :=
  of_group record089 2 (smallEmbedding record089) (small_cells_exact record089 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record089_frame002_indices record089_frame002_graph record089_frame002_links
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (Fin.cases (record089_frame001_supported hcells) (Fin.cases (record089_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x74570665361d6075a856a55c53e50e5075024da49948f46a44c4384013ed3e03d33b138937f3403343283213072ed2e62e02db2cd21920c1fb1ef1e11d61d01b417d17515214d1421351170f20e10cb0c60c108d08b08607d06c06a06705d05a05805405305205104503d03a03503303002e02c02702402202101e01d01c01901201000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (smallEmbedding record090) (small_cells_exact record090 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbf4aae97c93f92785e8217a776b7537115dc5ac5964eb4c146343a4253fb38737a33031e2922851b31a618717816a1451351240f70ea0db0a90a80a709c09409008c08807806e06a06906605a05505405004003603203102e02201d01c01901701601200e00d009008007005004002001000 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x5d72de969cb254da2214fa47bb3ad9d30e6e60b2ef16d4a044d725911c48924261e30d9c6c230517b0b605922bf136097c48c239118888433618f0bc05b02c8154083024011a08c04402140d406902d81680ac05502a014c0a004d01a80c8062026011808804201e00e807003201700b005002600e00680240100070018008002000 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x63a30f141e9d74d9a67d2ce94b4a2a48520a8ff45d2060eb86c032098b0bea5cf2df94a8a044e026891d88a4431211903c77a3861b00d40576293138898840e1e30e106d0340133092845c214104074838c16408d04601a80d206603201800b605a02b01540a8053027010c07203501900c405c02c014008c04401e00e8070032017009803801a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (smallEmbedding record094) (small_cells_exact record094 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
def record097_frame001_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6652a2549aa104fd27193208f945622690827fa3f49f58aaa51926e131892445c1e28de06cc30d1630ad454424d11f08c445420d10307e83e41e50eb074038e1c00da06b033e1900c5057c2b013d097848423211308603d81e00e9046823011606d03501a40cc064030016c0b405602a81500a603501900c405c02c014008c04401e00e807003601a00c805c0260110070034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record097_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record097_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record097) (record097.maps 1)
      (record097.inverseMaps 1) record097_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record097_frame001_links_0000 record097_frame001_links_0064)
theorem record097_frame001_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 1 :=
  of_group record097 1 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record097_frame001_indices record097_frame001_graph record097_frame001_links
def record097_frame002_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x63cab19562a9c544291d40496348d242916086742ba128cce65231f18bcbee5c22a114249f84b523e11bc8c842c2008f5077e36b1ae8cfc65e30e1768b745942bc14f0a384da24c11e08143e21a20be055c28e13c09884281fe0f4046823011606d03501a40cc064030016c0b405602a81500a603501900c405c02c014008c04401e00e807003601a00c805c0260110070034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record097_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record097_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record097) (record097.maps 2)
      (record097.inverseMaps 2) record097_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record097_frame002_links_0000 record097_frame002_links_0064)
theorem record097_frame002_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 2 :=
  of_group record097 2 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record097_frame002_indices record097_frame002_graph record097_frame002_links
def record097_frame003_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xad54327b4e19b5316594718a1122083ef7ccf799f32962cc41802f1576a894da6f4a692d21a083fa7d0f71de3a4718df9b3350684cb98c3005ecb71642ba4988d1011ec3b0730dd1a62e0578a60ea1d03985f0b816c2c0560a813c2704a092120238330600bc1602a05008c1101e03a0700d81a03205c0981101c0340600901001c0280400600800800 } : Fields).get c.val)
theorem record097_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record097) (record097.maps 3) (record097.inverseMaps 3) record097_frame003_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record097) (record097.maps 3) (record097.inverseMaps 3) record097_frame003_indices (Fin.ofNat record097.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record097_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record097) (record097.maps 3)
      (record097.inverseMaps 3) record097_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record097_frame003_links_0000 record097_frame003_links_0064)
theorem record097_frame003_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 3 :=
  of_group record097 3 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record097_frame003_indices record097_frame003_graph record097_frame003_links
def record097_frame004_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x6b4c79882ff5f2bc573ac655eaa94927c4e89c10ea0c3fc7e0f69e63826bcd498f2f25ccb795129a520a29372644b89412022c4448690920a4047c0f01d6344660c01742c8580ad15026c4c0930ea1d0398600bc1742d0580a813c2704a092120238340640c41702c05008c1101e03a0700d81a03205c0981101c0340600901001c0280400600800800 } : Fields).get c.val)
theorem record097_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record097) (record097.maps 4) (record097.inverseMaps 4) record097_frame004_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record097) (record097.maps 4) (record097.inverseMaps 4) record097_frame004_indices (Fin.ofNat record097.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record097_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record097) (record097.maps 4)
      (record097.inverseMaps 4) record097_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record097_frame004_links_0000 record097_frame004_links_0064)
theorem record097_frame004_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 4 :=
  of_group record097 4 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record097_frame004_indices record097_frame004_graph record097_frame004_links
def record097_frame005_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x770d71a9b46684ce598314606c0575ad35a0b292f2534909111da3241e7f0fc9e53aa748e61b534c668c91762e2590b095228e50c9e93725c4a08e9102123b0748d719830c5f8b91662904f0980f61e83c8630c017c2e05a0ac1482884d09812c250340620c01682b04e0881081e03a0700d81a03205c0981101c0340600901001c0280400600800800 } : Fields).get c.val)
theorem record097_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record097) (record097.maps 5) (record097.inverseMaps 5) record097_frame005_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record097) (record097.maps 5) (record097.inverseMaps 5) record097_frame005_indices (Fin.ofNat record097.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record097_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record097) (record097.maps 5)
      (record097.inverseMaps 5) record097_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record097_frame005_links_0000 record097_frame005_links_0064)
theorem record097_frame005_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 5 :=
  of_group record097 5 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record097_frame005_indices record097_frame005_graph record097_frame005_links
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (Fin.cases (record097_frame001_supported hcells) (Fin.cases (record097_frame002_supported hcells) (Fin.cases (record097_frame003_supported hcells) (Fin.cases (record097_frame004_supported hcells) (Fin.cases (record097_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
def record098_frame001_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33258a4aad526a83d3f49c64b524bd23a8ad44ca104fac7b63d39c78af251926d93189244361fd8fa46f23651868a8850427312688f843820d10007943ae1cf0e387003681ac0cf85d02dc15f0ac04f425e12808c844c20a0f607803a412208c04582000dc06d03481980c805f02e01680ac05502a014c09003601a80c405c02c013809004401e00e807003601a00c805c0240110078034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record098_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record098_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record098) (record098.maps 1)
      (record098.inverseMaps 1) record098_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record098_frame001_links_0000 record098_frame001_links_0064)
theorem record098_frame001_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) : Supported record098 1 :=
  of_group record098 1 (smallEmbedding record098) (small_cells_exact record098 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record098_frame001_indices record098_frame001_graph record098_frame001_links
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (Fin.cases (record098_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000
